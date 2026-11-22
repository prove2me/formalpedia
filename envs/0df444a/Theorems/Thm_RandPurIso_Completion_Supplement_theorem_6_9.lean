-- Prove2me | Theorems.Thm_RandPurIso_Completion_Supplement_theorem_6_9
-- name    : RandPurIso.Completion.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:54:22.802299+00:00
-- url     : https://prove2.me/theorems/f49eca04-4b1f-45f8-9d02-5cfd748d0db7
-- title:
--   Theorem 6.9 — $t$ copies of $\rho$ simulate $t$ queries to a random state preparation unitary
-- statement:
--   There are absolute constants $C_0$, $C$, $k$ such that the following holds. Let $1\le N\le D$, $t<ND$ and $\varepsilon>0$, and let $\mathcal A$ be an oracle circuit on $n$ qubits making at most $t$ uncontrolled forward queries to a unitary acting on $\mathcal H([N])\otimes\mathcal H([D])$. There is a circuit $\mathcal B$, independent of $\rho$ and taking exactly $t$ copies of $\rho$, of size at most
--
--   $$
--   C\big(|\mathcal A|+\log N+\log D+\log(1/\varepsilon)+2\big)^k ,
--   $$
--
--   such that for every $N$-dimensional mixed state $\rho$,
--
--   $$
--   \mathrm{TD}\Big(\mathop{\mathbb E}_{U^\rho\leftarrow\mathcal D^\rho}\big[\mathcal A^{U^\rho}\big],\ \mathcal B(\rho^{\otimes t})\Big)\le\varepsilon+C_0\,\frac{t}{\sqrt{ND-t}} ,
--   $$
--
--   where $\mathcal D^\rho$ first chooses a Haar-random purification $|\psi_\rho\rangle$ of $\rho$ on $\mathcal H([N])\otimes\mathcal H([D])$ and then a Haar-random unitary completion of $|0\rangle\mapsto|\psi_\rho\rangle$: concretely $U^\rho=(I_N\otimes W)D_0(I\oplus U)$ with $W\leftarrow\mathrm{Haar}(\mathrm U(D))$, $U\leftarrow\mathrm{Haar}(\mathrm U(ND-1))$, for any fixed purification $\psi_0$ and completion $D_0$ of $|0\rangle\mapsto\psi_0$.
--
--   The theorem lifts copy-complexity lower bounds for mixed states to lower bounds for purified query access (Corollary 6.10).
--
--   **Formalization Note** $\mathcal A$ and $\mathcal B$ are Clifford+T circuits (the base mission's `QInstr`). $\mathcal A$ starts on $|0^n\rangle$ and its output is its final $n$-qubit state; a query applies `qubitChannel U` on $\lceil\log_2(ND+1)\rceil$ qubits (binary encoding, $\bot=\mathrm{bin}(ND)$). $\mathcal B$ has no oracle and runs on $|0^n\rangle\otimes\rho^{\otimes t}\otimes|0^a\rangle$; its output is its first $n$ qubits. $|\mathcal A|$ is the instruction count plus $n$; logarithms are $\lceil\log_2\cdot\rceil$, and $\log(1/\varepsilon)$ is $\lceil\log_2\lceil1/\varepsilon\rceil\rceil$. The expectation is a Bochner integral against the product Haar measure.
--
--   Differences from the source:
--   - reading: B of size poly(|A|, log N, log D, log(1/ε)) → B's instruction count and its qubits other than the t input copies (n + a) are ≤ C(|A| + ⌈log₂N⌉ + ⌈log₂D⌉ + ⌈log₂⌈1/ε⌉⌉ + 2)^k with absolute C, k (|A| = instruction count + n); reason: the base mission's reading of 'poly'; the t·⌈log₂N⌉ input wires cannot be counted, since t is not bounded by |A| (A with one qubit and no gates, N = 2, t = 2D − 1 would force width ≥ t while poly(1, 1, log D, log 1/ε) is polylog D)
--   - reading: ≤ ε + O(t/√(N·D − t)) → ≤ ε + C₀ t/√(N·D − t) with one absolute C₀ chosen before N, D, t, ε and A; reason: the O(·) of Theorem 5.4, from which the bound is inherited
--   - generalization: there exists a distribution D^ρ (Haar purification, then Haar completion), the purification obtained from 'any fixed purification' (Lemma 6.8) → the bound for the explicit D^ρ given by (I ⊗ W) D₀ (I ⊕ U), for every purification ψ₀ of ρ and every completion D₀ of |0⟩ ↦ ψ₀; reason: names the distribution the page describes and asserts the bound for every fixed purification and completion; this implies the existential statement and the page's description
--   - encoding: oracle circuit A making uncontrolled forward queries to a unitary on H([N]) ⊗ H([D]); circuit B taking t copies of ρ → Clifford+T circuits (QInstr); A on n qubits from |0^n⟩ with queries qubitChannel U on ⌈log₂(ND+1)⌉ qubits (⊥ = bin(ND)) and output its n qubits; B on n + (t⌈log₂N⌉ + a) qubits from |0^n⟩ ⊗ ρ^{⊗t} ⊗ |0^a⟩, output its first n qubits; reason: the base mission's circuit and query conventions (Theorem 5.4)
--   - encoding: N-dimensional mixed state ρ → a density matrix on Fin N with N ≥ 1, written in binary on ⌈log₂N⌉ qubits; reason: an N-dimensional space is nonempty; same instances
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 6.9, p. 43

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_RandPurIso_Completion_traceDist
import Definitions.Def_RandPurIso_Completion_QInstr
import Definitions.Def_RandPurIso_Completion_qubitChannel
import Definitions.Def_RandPurIso_Completion_simQueryChannel
import Definitions.Def_RandPurIso_Completion_IsCompletion
import Definitions.Def_RandPurIso_Completion_randomCompletion
import Definitions.Def_RandPurIso_Completion_Supplement_hiddenPairMeasure
import Definitions.Def_RandPurIso_Completion_Supplement_prepUnitary
import Definitions.Def_RandPurIso_Completion_Supplement_copyInput
open Matrix MeasureTheory
open ShiShallow
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Theorem 6.9** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §6.2, p. 43).

Let `D ≥ N`, `t < N·D` and `ε > 0`. Let `A` be an oracle circuit which makes at most `t` uncontrolled
forward queries to a unitary acting on `H([N]) ⊗ H([D])`. There exists a circuit `B` of size
`poly(|A|, log N, log D, log(1/ε))`, independent of `ρ` and taking exactly `t` copies of `ρ`, such that
for every `N`-dimensional mixed state `ρ`, with `D^ρ` the distribution that first chooses a
Haar-random purification `|ψ_ρ⟩` and then a Haar-random unitary completion of `|0⟩ ↦ |ψ_ρ⟩`,
`TD(E_{U^ρ ← D^ρ}[A^{U^ρ}], B(ρ^{⊗t})) ≤ ε + O(t / √(N·D − t))`.

**Formalization Note.**
* `O(·)` is one absolute constant `C₀`; `poly` is `C (·)^k` with absolute `C, k` (base mission's
  reading of Theorem 5.4); all three are chosen before `N, D, t, ε` and `A`. `log(1/ε)` is
  `⌈log₂ ⌈1/ε⌉⌉`, `log N`, `log D` are `⌈log₂ ·⌉`, and `|A|` is `A`'s instruction count plus its number of
  qubits `n`. "N-dimensional" gives `N ≥ 1`.
* `A` is a Clifford+T oracle circuit on `n` qubits started on `|0^n⟩`, whose output is its final
  `n`-qubit state. Its query to `U` on `H([N]) ⊗ H([D]) ≅ H([N·D])` (`finProdFinEquiv`) is
  `qubitChannel U` on `⌈log₂(N·D + 1)⌉` qubits with binary encoding and `⊥ = bin(N·D)` (the base
  mission's `simQueryChannel` convention).
* `B` is a Clifford+T circuit with no oracle on `n + (t·⌈log₂ N⌉ + a)` qubits, fixed before `ρ`, run on
  `|0^n⟩ ⊗ ρ^{⊗t} ⊗ |0^a⟩` (`ρ` in binary on `⌈log₂ N⌉` qubits); its output is its first `n` qubits.
  Size: its instruction count and its qubits other than the `t` input copies (`n + a`) are bounded;
  the `t·⌈log₂ N⌉` input wires are not counted, since `t` is not bounded by `|A|`.
* `D^ρ`: for every purification `ψ₀` of `ρ` and every completion `D₀` of `|0⟩ ↦ ψ₀`, `U^ρ =
  (I_N ⊗ W) D₀ (I ⊕ U)` with `W` Haar on `U(D)` and `U` Haar on `U(N·D − 1)` independent
  (`prepUnitary`); the expectation is the Bochner integral against the product Haar measure, of a
  continuous integrand on a compact group. -/
theorem theorem_6_9 :
    ∃ C₀ : ℝ, ∃ C k : ℕ, ∀ N D t : ℕ, 1 ≤ N → N ≤ D → t < N * D → ∀ ε : ℝ, 0 < ε →
      ∀ (n : ℕ) (A : List (QInstr 1 (fun _ => qw (N * D)) n)), QInstr.queryCount 0 A ≤ t →
        ∃ (a : ℕ) (B : List (QInstr 0 (fun _ => 0) (n + (t * Nat.clog 2 N + a)))),
          (B.length : ℝ) ≤ C * ((A.length : ℝ) + n + Nat.clog 2 N + Nat.clog 2 D +
            Nat.clog 2 ⌈1 / ε⌉₊ + 2) ^ k ∧
          ((n + a : ℕ) : ℝ) ≤ C * ((A.length : ℝ) + n + Nat.clog 2 N + Nat.clog 2 D +
            Nat.clog 2 ⌈1 / ε⌉₊ + 2) ^ k ∧
          ∀ ρ : Matrix (Fin N) (Fin N) ℂ, PeresTerno.IsDensityMatrix ρ →
          ∀ ψ₀ : Fin (N * D) → ℂ, IsPurification (D := D) ρ ψ₀ →
          ∀ D₀ : Matrix.unitaryGroup (Fin (N * D)) ℂ, IsCompletion (purifIso ψ₀) D₀ →
            traceDist
              (∫ p, QInstr.evalList
                  (fun _ => qubitChannel (prepUnitary D₀ p.1 p.2)
                    (fun x => binEnc (qw (N * D)) x.val) (fun x => binEnc (qw (N * D)) x.val)
                    (binEnc (qw (N * D)) (N * D)))
                  A (Matrix.single (zeroBits n) (zeroBits n) 1)
                ∂((QAlgorithms.Schur.unitaryHaar D).prod (QAlgorithms.Schur.unitaryHaar (N * D - 1))))
              (outputPart (QInstr.evalList (fun j => Fin.elim0 j) B (copyInput n a t ρ)))
              ≤ ε + C₀ * t / Real.sqrt ((N : ℝ) * D - t) := by sorry

end RandPurIso.Completion.Supplement
