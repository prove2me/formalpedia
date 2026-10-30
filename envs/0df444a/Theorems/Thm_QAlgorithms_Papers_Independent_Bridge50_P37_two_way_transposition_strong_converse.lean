-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_two_way_transposition_strong_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.two_way_transposition_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:47:50.445512+00:00
-- url     : https://prove2.me/theorems/8c427fec-d4b5-429e-bad2-2b3b1e5b2e16
-- title:
--   Theorem 7: two-way capacity and exponential strong converse transposition bound
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   For a channel $T:M_{d_1}\to M_{d_2}$ put $b=\log_2\|\vartheta_{d_2}\circ T\|_\diamond$. Its two-way LOCC-assisted quantum capacity satisfies
--   $$Q_2(T)\le b.$$
--   For every sequence of actual two-way schemes with parameters $(N_\nu,m_\nu,\epsilon_\nu)$, if $m_\nu\to\infty$ and
--   $$\liminf_{\nu\to\infty}\frac{\log_2N_\nu}{m_\nu}>b,$$
--   then $\epsilon_\nu\to1$ exponentially: there exist $c>0$ and $\nu_0$ such that $1-\epsilon_\nu\le e^{-cm_\nu}$ for every $\nu\ge\nu_0$. The capacity uses vanishing errors and a limsup achievable rate, distinct from this liminf lower rate.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 12, Theorem 7: two-way capacity and exponential strong converse transposition bound

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 7, PDF pp.12--13: two-way capacity bound and exponential strong converse.
Achievability uses limsup, whereas the strong-converse hypothesis uses liminf. -/
theorem two_way_transposition_strong_converse (d1 d2 : ℕ) [NeZero d1] [NeZero d2]
    (T : MatrixMap (Fin d1) (Fin d2)) (hT : IsChannel T) :
    diamondAssistedCapacity T false ≤ Real.logb 2 (diamond ((basisTransposeLinearMap (Fin d2)).comp T)) ∧
    AssistedStrongConverse T false (Real.logb 2 (diamond ((basisTransposeLinearMap (Fin d2)).comp T))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
