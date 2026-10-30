-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_pinch_fidelity_lift
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.pinch_fidelity_lift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:38:39.524193+00:00
-- url     : https://prove2.me/theorems/9fec743d-25bd-4c35-a5e1-60c10c5077cd
-- title:
--   Lift a block-diagonal approximation through rank-one pinching
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Let $\rho_{AR}$ be a density operator and let $\{|y\rangle\}_y$ be any orthonormal basis of $A$. Write $P_y=|y\rangle\langle y|$ and $\mathcal E(\omega)=\sum_y(P_y\otimes I_R)\omega(P_y\otimes I_R)$; put $\rho'=\mathcal E(\rho)$. Let $\epsilon\ge0$ and let the normalized density $\sigma'$ have the classical-quantum form $\sum_yp_y|y\rangle\langle y|\otimes\sigma_R^y$, equivalently $\sigma'=\mathcal E(\sigma')$. If $F(\sigma',\rho')\ge1-\epsilon$, then there exists a normalized density $\sigma$ such that
--
--   $$
--   F(\sigma,\rho)\ge1-\epsilon,\qquad \sigma'=\mathcal E(\sigma).
--   $$
--
--   Here $F(\alpha,\beta)=\|\sqrt\alpha\sqrt\beta\|_1^2$ is squared fidelity. No purity assumption on $\rho$ is imposed.
--
--   The approximation has an actual preimage with the prescribed pinched state.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 25, Lemma 4.13

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 4.13, PDF pp.25--26: fidelity lifting for an arbitrary rank-one basis measurement.
The PDF p.26 has sigmaPrime on the LEFT: sigmaPrime = rankOnePinching U sigma.
The fixed-point premise on sigmaPrime is exactly its displayed normalized cq form.
Fidelity is SQUARED rootFidelity, in accordance with Definition 2.3. No purity premise. -/
theorem pinch_fidelity_lift {A R : Type} [Fintype A] [Fintype R]
    [DecidableEq A] [DecidableEq R] [Nonempty A] [Nonempty R]
    (rho sigmaPrime : Matrix (A × R) (A × R) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigmaPrime)
    (U : Matrix.unitaryGroup A ℂ) (hblock : sigmaPrime = rankOnePinching U sigmaPrime)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hclose : 1 - eps ≤ rootFidelity sigmaPrime (rankOnePinching U rho) ^ 2) :
    ∃ sigma : Matrix (A × R) (A × R) ℂ, IsDensityMatrix sigma ∧
      1 - eps ≤ rootFidelity sigma rho ^ 2 ∧ sigmaPrime = rankOnePinching U sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
