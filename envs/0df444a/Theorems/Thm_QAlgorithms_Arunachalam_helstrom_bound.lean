-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_helstrom_bound
-- name    : QAlgorithms.Arunachalam.helstrom_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:55:13.556839+00:00
-- url     : https://prove2.me/theorems/cbd03fca-c022-410c-bf0a-4d4844ef94d9
-- title:
--   Helstrom bound for guessing a uniform bit from |ψ_b⟩, and its corollary
-- statement:
--   Let $|\psi_0\rangle,|\psi_1\rangle$ be pure states (unit vectors) in a finite-dimensional Hilbert space, and let $b\in\{0,1\}$ be uniformly distributed. An algorithm that receives $|\psi_b\rangle$ and guesses $b$ is a two-outcome POVM $\{M_0,M_1\}$; it guesses correctly with probability $P=\tfrac12\langle\psi_0|M_0|\psi_0\rangle+\tfrac12\langle\psi_1|M_1|\psi_1\rangle$. Then for every such POVM:
--
--   1. $$
--   P\le\frac12+\frac12\sqrt{1-|\langle\psi_0|\psi_1\rangle|^2};
--   $$
--   2. for every $\delta\in[0,1/2]$, if $P\ge1-\delta$ then $|\langle\psi_0|\psi_1\rangle|\le2\sqrt{\delta(1-\delta)}$.
--
--   This is the source of the $\log(1/\delta)$ terms of the sample complexity lower bounds (Lemmas 7.4.1 and 7.4.2).
--
--   **Formalization Note** Any ancilla, unitary or classical post-processing of the algorithm is absorbed into the POVM. The restriction $\delta\le1/2$ in part 2 is implicit in the source: for $\delta>1/2$ and $\psi_0=\psi_1$ a blind guess succeeds with probability $1/2\ge1-\delta$ while $2\sqrt{\delta(1-\delta)}<1$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 162, Fact 7.3.9. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false

namespace QAlgorithms.Arunachalam






/-- Arunachalam p.162, Fact 7.3.9 (Helstrom bound): let `b ∈ {0,1}` be uniform and let an
algorithm, given the pure state `|ψ_b⟩`, guess `b`; its guess is the outcome of a two-outcome
POVM `{M_0, M_1}` (ancillas and unitaries absorbed). Then
1. it guesses correctly with probability at most `1/2 + (1/2)√(1 − |⟨ψ_0|ψ_1⟩|²)`;
2. if it guesses correctly with probability `≥ 1 − δ`, then `|⟨ψ_0|ψ_1⟩| ≤ 2√(δ(1 − δ))`.

In part 2 we assume `δ ∈ [0, 1/2]`, which the source leaves implicit: for `δ > 1/2` the
conclusion fails at `ψ_0 = ψ_1` (any blind guess succeeds with probability `1/2 ≥ 1 − δ`). -/
theorem helstrom_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : Bool → EuclideanSpace ℂ ι) (hψ : ∀ b, IsState (ψ b))
    (M : Bool → Matrix ι ι ℂ) (hM : IsPOVM M) :
    ensembleSuccess (fun _ => (1 / 2 : ℝ)) ψ M ≤
        1 / 2 + 1 / 2 * Real.sqrt (1 - ‖inner ℂ (ψ false) (ψ true)‖ ^ 2) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → 1 - δ ≤ ensembleSuccess (fun _ => (1 / 2 : ℝ)) ψ M →
        ‖inner ℂ (ψ false) (ψ true)‖ ≤ 2 * Real.sqrt (δ * (1 - δ)) := by
  sorry

end QAlgorithms.Arunachalam
