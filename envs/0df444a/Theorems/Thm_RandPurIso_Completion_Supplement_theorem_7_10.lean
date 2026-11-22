-- Prove2me | Theorems.Thm_RandPurIso_Completion_Supplement_theorem_7_10
-- name    : RandPurIso.Completion.Supplement.theorem_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:57:18.757298+00:00
-- url     : https://prove2.me/theorems/c0264735-ee2c-4d58-8c7b-8628fe52487c
-- title:
--   Theorem 7.10 — the search channel $\mathcal C_z$: perfect recovery from dilation or switch queries, $\Pr[\mathcal A^{\mathcal C_z}=z]\le 2^{-m}+4mq^{3/2}/\sqrt L$ from channel queries
-- statement:
--   Let $m\ge1$, $L\ge1$, $d\ge2$, let $z\leftarrow\{0,1\}^m$ be uniform and let the hidden pairs of $m$ independent instances $(\mathsf{SAME}_i,\mathsf{DIFF}_i)$ be sampled independently of $z$. Let $\mathcal C_z$ be the search channel. Then:
--
--   1. an efficient algorithm recovers $z$ with probability one using $2m$ forward queries to any fixed isometry dilation of $\mathcal C_z$; another efficient algorithm recovers $z$ with probability one using $m$ applications of $\mathrm{Sw}[\mathcal C_z,\mathcal C_z]$;
--   2. any algorithm $\mathcal A$ making at most $q\ge0$ forward channel queries satisfies
--   $$
--   \Pr\big[\mathcal A^{\mathcal C_z}=z\big]\le 2^{-m}+\frac{4mq^{3/2}}{\sqrt L},
--   $$
--   where the probability is averaged over $z$, the hidden pairs and the algorithm's randomness;
--   3. the input and output dimensions of $\mathcal C_z$ are $m(Ld+1)$, and $\mathcal C_z$ has an isometry dilation whose environment has dimension $(m(Ld+1))^2$.
--
--   The theorem turns the SAME/DIFF decision problem into a search problem in which channel queries have exponentially small success probability while two dilation queries or one switch per bit suffice.
--
--   **Formalization Note** *Efficient*: a Clifford+T oracle circuit on $m+a$ qubits started on $|0\cdots0\rangle$, with instruction count and width at most $C(m+\lceil\log_2(m(Ld+1))\rceil+\lceil\log_2 e\rceil+2)^k$ for absolute $C,k$ ($e$ the environment dimension; dropped for the switch variant), fixed before $z$, the hidden pairs and the dilation, making exactly $2m$ (resp. $m$) queries; the first $m$ qubits of its final state hold $z$ with probability $1$. A dilation is any isometry $W:\mathcal H([m])\otimes\mathbf{In}\to(\mathcal H([m])\otimes\mathbf{In})\otimes\mathcal H([e])$, any $e$, with $\mathrm{Tr}_E(W\rho W^\dagger)=\mathcal C_z(\rho)$, queried through the binary encoding `dilQuery`; switch queries go through `swQuery`. In clause 2, $\mathcal A$ is the base mission's `OracleAlg` with workspace $\{0,1\}^m\times W'$; its guess is the $\{0,1\}^m$ register and $\Pr[\mathcal A^{\mathcal C_z}=z]$ is the diagonal weight of its final state on guess $z$, averaged by $2^{-m}\sum_z$ and a Bochner integral over the $mL$ Haar unitaries.
--
--   Differences from the source:
--   - reading: an efficient algorithm → a Clifford+T oracle circuit with instruction count and width ≤ C(m + ⌈log₂(m(Ld+1))⌉ + ⌈log₂ e⌉ + 2)^k, absolute C, k, fixed before z, the hidden pairs and the dilation, making exactly 2m (resp. m) queries; reason: the base mission's reading of 'efficient' (Theorem 5.4)
--   - encoding: any fixed isometry dilation of C_z; m applications of Sw[C_z, C_z] → every isometry W into (H([m]) ⊗ In) ⊗ H([e]), every e, with Tr_E(WρW†) = C_z(ρ), queried by dilQuery (binary encoding, environment wires input |0…0⟩, failure flag); Sw[C_z, C_z] from the Kraus family of the natural dilation, queried by swQuery; reason: every finite environment is a relabelling of some H([e]); the switch does not depend on the Kraus representation
--   - encoding: recovers z with probability one; Pr[A^{C_z} = z] averaged over z, the hidden pairs and the algorithm's randomness → diagonal weight 1 on z of the first m output qubits; for clause 2, (1/2^m) Σ_z ∫ (Σ diagonal weight of A's final state on guess register = z) d(searchMeasure); reason: A's randomness is inside its CPTP steps and mixed initial state; same instances
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 7.10, p. 58 (§7.3)

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_QInstr
import Definitions.Def_RandPurIso_Completion_Supplement_IsDilation
import Definitions.Def_RandPurIso_Completion_Supplement_chanOracle
import Definitions.Def_RandPurIso_Completion_Supplement_searchChannel
import Definitions.Def_RandPurIso_Completion_Supplement_searchEnc
open Matrix MeasureTheory
open ShiShallow

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Theorem 7.10** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7.3, p. 58).

Let `m ≥ 1`, `L ≥ 1`, `d ≥ 2`, `z ← {0,1}^m` uniform, and `m` independent families of hidden pairs.
An efficient algorithm recovers `z` with probability one using `2m` forward queries to any fixed
isometry dilation of `C_z`, or `m` applications of `Sw[C_z, C_z]`. In contrast, any algorithm `A`
making at most `q ≥ 0` forward channel queries satisfies `Pr[A^{C_z} = z] ≤ 2^{−m} + 4 m q^{3/2} / √L`,
the probability averaged over `z`, the hidden pairs and the algorithm's randomness. The input and
output dimensions are `m(Ld + 1)`, and a common dilation environment can be fixed to the square of
this dimension.

**Formalization Note.**
* *Efficient* (base mission's reading of "efficient"/"poly"): a Clifford+T oracle circuit
  (`QInstr`) on `m + a` qubits, started on `|0…0⟩`, whose instruction count and number of qubits are
  `≤ C (m + ⌈log₂(m(Ld+1))⌉ + ⌈log₂ e⌉ + 2)^k` with absolute `C, k` (`⌈log₂ e⌉` dropped for the switch
  variant). The circuit is fixed before `z`, the hidden pairs and the dilation; it makes exactly `2m`
  queries (resp. `m`). "Recovers `z` with probability one": the first `m` qubits of the final state
  hold `z` with probability `1`.
* *Any fixed isometry dilation*: every isometry `W : H([m]) ⊗ In → (H([m]) ⊗ In) ⊗ H([e])`, every
  `e`, with `Tr_E(W ρ W†) = C_z(ρ)`, queried through `dilQuery` (binary encodings `cEnc`, environment
  wires input as `|0…0⟩`, failure flag). The switch is queried through `swQuery` (`Sw[C_z, C_z]` on
  `C ⊗ H([m]) ⊗ In`; the switch does not depend on the Kraus representation).
* *Lower bound*: `A` is any oracle algorithm of the base mission, fixed before `z` and the pairs;
  its randomness is inside its CPTP steps and initial state. Its guess is the classical register
  `Fin m → Bool` of its workspace `(Fin m → Bool) × W'`, and `Pr[A^{C_z} = z]` is the total diagonal
  weight of the final state on guess `z`, averaged over `z` (`2^{−m} Σ_z`) and over the pairs
  (Bochner integral against `searchMeasure`; the integrand is continuous on a compact group).
* *Dimensions*: `C_z` acts on `Fin m × In`, of cardinality `m(Ld + 1)`, and has an isometry dilation
  with environment `Fin ((m(Ld + 1))²)` for every `z` and every choice of hidden pairs. -/
theorem theorem_7_10 :
    (∃ C k : ℕ, ∀ m L d : ℕ, 1 ≤ m → 1 ≤ L → 2 ≤ d → ∀ e : ℕ,
      ∃ (a : ℕ) (c : List (QInstr 1 (fun _ => cw m L d + Nat.clog 2 e + 1) (m + a))),
        QInstr.queryCount 0 c = 2 * m ∧
        (c.length : ℝ) ≤ C * ((m : ℝ) + cw m L d + Nat.clog 2 e + 2) ^ k ∧
        ((m + a : ℕ) : ℝ) ≤ C * ((m : ℝ) + cw m L d + Nat.clog 2 e + 2) ^ k ∧
        ∀ (z : Fin m → Bool) (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ)
          (Wd : Matrix ((Fin m × InSp L d) × Fin e) (Fin m × InSp L d) ℂ),
          IsDilation Wd (searchChannel z U) →
          ∑ α : Bits a, QInstr.evalList (fun _ => dilQuery Wd) c
              (Matrix.single (zeroBits (m + a)) (zeroBits (m + a)) 1)
              (Fin.append z α) (Fin.append z α) = 1) ∧
    (∃ C k : ℕ, ∀ m L d : ℕ, 1 ≤ m → 1 ≤ L → 2 ≤ d →
      ∃ (a : ℕ) (c : List (QInstr 1 (fun _ => 1 + cw m L d + 1) (m + a))),
        QInstr.queryCount 0 c = m ∧
        (c.length : ℝ) ≤ C * ((m : ℝ) + cw m L d + 2) ^ k ∧
        ((m + a : ℕ) : ℝ) ≤ C * ((m : ℝ) + cw m L d + 2) ^ k ∧
        ∀ (z : Fin m → Bool) (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ),
          ∑ α : Bits a, QInstr.evalList (fun _ => swQuery z U) c
              (Matrix.single (zeroBits (m + a)) (zeroBits (m + a)) 1)
              (Fin.append z α) (Fin.append z α) = 1) ∧
    (∀ m L d q : ℕ, 1 ≤ m → 1 ≤ L → 2 ≤ d →
      ∀ (W' : Type) [Fintype W'] [DecidableEq W']
        (A : OracleAlg (Fin m × InSp L d) (Fin m × InSp L d) ((Fin m → Bool) × W')),
        A.numQueries ≤ q →
        (1 / 2 ^ m : ℝ) * ∑ z : Fin m → Bool,
            ∫ U, (∑ o : Fin m × InSp L d, ∑ w : W',
              A.run (chanOracle (searchChannel z U)) (o, (z, w)) (o, (z, w))).re
              ∂(searchMeasure m L d) ≤
          (1 / 2 ^ m : ℝ) + 4 * m * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt L) ∧
    (∀ m L d : ℕ, 1 ≤ m → 1 ≤ L → 2 ≤ d →
      Fintype.card (Fin m × InSp L d) = m * (L * d + 1) ∧
      ∀ (z : Fin m → Bool) (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ),
        ∃ V : Matrix ((Fin m × InSp L d) × Fin ((m * (L * d + 1)) ^ 2)) (Fin m × InSp L d) ℂ,
          IsDilation V (searchChannel z U)) := by sorry

end RandPurIso.Completion.Supplement
