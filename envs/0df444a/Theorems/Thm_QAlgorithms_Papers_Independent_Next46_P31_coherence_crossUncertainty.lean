-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_coherence_crossUncertainty
-- name    : QAlgorithms.Papers.Independent.Next46.P31.coherence_crossUncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:31:00.025408+00:00
-- url     : https://prove2.me/theorems/94a05d39-58c2-4350-afa3-7ea13442826e
-- title:
--   Equation (1.10): cross coherence/spread uncertainty inequalities
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ and $K_j\rho$ have trace-class bounded realizations for every canonical position and momentum coordinate. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$, $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, and $S_A=C_A/D_A$ on the nonzero-spread domain; $\|\cdot\|_2$ is the Hilbert–Schmidt norm. For the position family $X$ and momentum family $K$, both cross coherence/spread inequalities hold:
--
--   $$
--   C_X(\rho)D_K(\rho)\ge\frac12,\qquad C_K(\rho)D_X(\rho)\ge\frac12.
--   $$
--
--   These statements use the source’s dimension-independent constant and involve no division by a spread, so no nonzero-spread hypothesis is needed.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 4, Equation (1.10): cross coherence/spread uncertainty inequalities

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF p.4, (1.10): both cross inequalities with the printed constant 1/2. -/
theorem coherence_crossUncertainty {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d)) (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : CanonicallyRegular rho) :
    (1 : ℝ) / 2 ≤ coherenceLength b positionGraph rho * coherenceSpread b momentumGraph rho ∧
    (1 : ℝ) / 2 ≤ coherenceLength b momentumGraph rho * coherenceSpread b positionGraph rho := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
