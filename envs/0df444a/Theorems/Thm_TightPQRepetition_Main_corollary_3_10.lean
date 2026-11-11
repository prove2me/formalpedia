-- Prove2me | Theorems.Thm_TightPQRepetition_Main_corollary_3_10
-- name    : TightPQRepetition.Main.corollary_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:34:15.386846+00:00
-- url     : https://prove2.me/theorems/e3d550cb-ba2e-441e-bb5a-c9d8f7276706
-- title:
--   Corollary 3.10 — leakage of the rotation (corrected: finite-dimensional $\mathcal H$)
-- statement:
--   Let $\Pi_A,\Pi_B$ be Hermitian projectors on a finite-dimensional space, $\varepsilon,\delta\in(0,1)$, and $U=U_{\varepsilon,\delta}^{\Pi_B,\Pi_A}$ a unitary as in Theorem 3.9. If $|\psi\rangle=\sum_j\alpha_j|v_j\rangle\in\mathrm{im}(\Pi_A)$ is a state with $\sum_{j:\varsigma_j<\delta}|\alpha_j|^2\le p$, then
--   $$\|(I-\Pi_B)U|\psi\rangle\|_2^2\le p+2\varepsilon.$$
--   A singular value exactly equal to $\delta$ belongs to the large case. This bound controls the weight that the rotation fails to bring into $\mathrm{im}(\Pi_B)$.
--
--   Differences from the source:
--   - correction: a Hilbert space → every finite-dimensional complex inner product space, of any dimension; reason: as for Theorem 3.9
--   - generalization: the unitary selected by Theorem 3.9 → any unitary satisfying the displayed singular-value guarantees of Theorem 3.9; reason: the leakage estimate uses precisely those guarantees and unitarity, so it applies in particular to the source unitary
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Corollary 3.10, printed p. 13 / PDF p. 15

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Jordan

namespace TightPQRepetition.Main

/-- Corollary 3.10 (printed p. 13, PDF p. 15). -/
theorem corollary_3_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (PA PB : H →L[ℂ] H) (hA : IsHermitianProjector PA)
    (hB : IsHermitianProjector PB) (J : JordanDecomposition PA PB) (ε δ p : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (U : H →L[ℂ] H) (hU : IsRotationUnitary J ε δ U)
    (ψ : H) (hψ : ‖ψ‖ = 1) (hmem : PA ψ = ψ) (α : J.idx → ℂ)
    (hα : ψ = ∑ j, α j • J.v j)
    (hp : ∑ j, (if J.sv j < δ then ‖α j‖ ^ 2 else 0) ≤ p) :
    ‖U ψ - PB (U ψ)‖ ^ 2 ≤ p + 2 * ε := by sorry

end TightPQRepetition.Main
