-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_Supplement_theorem_6_1
-- name    : QuantumCycleColoring.FourColor.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:05.842879+00:00
-- url     : https://prove2.me/theorems/0bf114bf-c883-4f29-bf12-7a95df9bbbf0
-- title:
--   Theorem 6.1: a uniform $\Lambda$-energy bound for $q$-outcome POVMs is equivalent to the impossibility of $q$-colouring cycles
-- statement:
--   Fix an integer $q\ge2$. For a PSD matrix $\Lambda\in\mathbb C^{N\times N}$ and a PSD operator $P$ on $\mathbb C^N\otimes\mathbb C^N$, write $\mathcal E_\Lambda(P)=\mathrm{Tr}(\Lambda A\Lambda B)$ for the **$\Lambda$-energy**, where $A=\mathrm{Tr}_{\mathcal A}((\Lambda^2\otimes I)P)^\top$ and $B=\mathrm{Tr}_{\mathcal B}((I\otimes\bar\Lambda^2)P)$. The following two statements are equivalent.
--
--   1. **(Q1)** There is a constant $C_q>0$ such that for every local dimension $N$, every PSD $\Lambda\in\mathbb C^{N\times N}$ with $\|\Lambda\|_F=1$ and every $q$-outcome POVM $\{P_i\}_{i\in[q]}$ on $\mathbb C^N\otimes\mathbb C^N$,
--   $$\sum_{i\in[q]}\mathcal E_\Lambda(P_i)\ \ge\ C_q.$$
--   2. **(Q2)** No one-way one-round anonymous quantum algorithm $q$-colours directed cycles with high probability: for every algorithm family (a state $\rho_n$ on finite registers $A^{(n)}B^{(n)}$ and a $q$-outcome POVM on $B^{(n)}_{\ell-1}A^{(n)}_\ell$ for each cycle length $n$, the same at every node), there are no constants $A,k>0$ and $n_0$ with $\Pr[\text{proper }q\text{-colouring of the }n\text{-cycle}]\ge1-A/n^k$ for all $n\ge n_0$.
--
--   The constant $C_q$ depends on $q$ alone. The success probability in (Q2) is the Born-rule probability of the $n$-node experiment, defined independently of the energy. The theorem reduces the distributed impossibility question for every number of colours to a single inequality about POVMs, the form in which the four-colour case is attacked.
--
--   Differences from the source:
--   - encoding: Λ-energy E_Λ(P) = Tr(ΛAΛB), a complex trace that is real for PSD P, Λ → energy Λ P is the real part of this trace; reason: the trace is real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N, colours [q] → vectors indexed by an arbitrary finite type d (N = card d), matrices indexed by d × d with the Kronecker product for ⊗, colours Fin q; reason: relabelling of bases and colours; the same instances
--   - reading: "succeeds with high probability", i.e. with probability at least 1 − 1/poly(n) (Definition 3.8, p.19) → there are real A > 0, k > 0 and a threshold n₀ ≥ 3 with success probability ≥ 1 − A/n^k for every n ≥ n₀; reason: 1/poly(n) read as an inverse-polynomial failure bound fixed before n; the proof's construction (success ≥ 1 − 1/n, p.42) meets it and the forward bound (1 − C_q)^⌊n/3⌋ → 0 (p.41) excludes it
--   - reading: a one-way one-round anonymous quantum algorithm (Definition 3.10; nodes know n, unbounded finite local computation) → a family giving, for each cycle length n, finite kept and message registers, a density matrix on them and a q-outcome POVM on (received message, kept register), identical at every node, with no computability requirement on n ↦ data; reason: this is the general finite-dimensional form used in the proof on p.41 (randomness and workspace absorbed), and n-dependence is allowed because nodes know n; footnote 10 shows the converse algorithm can be taken uniform, so the equivalence holds under either reading of uniformity
--   - encoding: cycle lengths n ≥ 3 → n = m + 3 with m : ℕ; reason: the same lengths, and ZMod (m + 3) needs no nonzero side condition
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Theorem 6.1, pp.40–41 (proof pp.41–42, footnote 10 p.42); model: Definitions 3.8–3.10, pp.19–20

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm
import Definitions.Def_QuantumCycleColoring_FourColor_Supplement_AlgorithmFamily

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor.Supplement

open QuantumCycleColoring.FourColor Matrix

/-- Theorem 6.1, pp.40–41 (Gur–Li, STOC 2027 #515). For every fixed integer `q ≥ 2` the
following are equivalent:
(Q1) there is a constant `C_q > 0` such that for every finite local dimension, every PSD `Λ`
with `‖Λ‖_F = 1` and every `q`-outcome POVM `{P_i}` on `ℂ^N ⊗ ℂ^N`, `∑_i E_Λ(P_i) ≥ C_q`;
(Q2) no one-way one-round anonymous quantum algorithm `q`-colours directed cycles with high
probability (success probability `≥ 1 − A/n^k` for some `A, k > 0` and all large `n`). -/
theorem theorem_6_1 (q : ℕ) (hq : 2 ≤ q) :
    (∃ C : ℝ, 0 < C ∧
      ∀ (d : Type) [Fintype d] [DecidableEq d] (Λ : Matrix d d ℂ), Λ.PosSemidef →
        frobNorm Λ = 1 →
        ∀ (P : Fin q → Matrix (d × d) (d × d) ℂ), FuchsVdGraaf.IsPOVM P →
        C ≤ ∑ i, energy Λ (P i)) ↔
    (∀ F : AlgorithmFamily q, ¬ F.SolvesWHP) := by sorry

end QuantumCycleColoring.FourColor.Supplement
