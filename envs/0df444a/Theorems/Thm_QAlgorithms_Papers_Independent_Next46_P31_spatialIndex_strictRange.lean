-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_spatialIndex_strictRange
-- name    : QAlgorithms.Papers.Independent.Next46.P31.spatialIndex_strictRange
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:34:49.639734+00:00
-- url     : https://prove2.me/theorems/870c8ac8-94ca-4fdb-9691-41e84ecc9429
-- title:
--   Unnumbered introduction result: strict spatial-index range and pure states
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ has a trace-class bounded realization for every canonical position coordinate; no momentum regularity is required. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$, $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, and $S_A=C_A/D_A$ on the nonzero-spread domain; $\|\cdot\|_2$ is the Hilbert–Schmidt norm. On the inherited domain $D_X(\rho)\ne0$, the canonical spatial index satisfies
--
--   $$
--   0<S_X(\rho)\le1,\qquad \rho\text{ pure}\ \Longrightarrow\ S_X(\rho)=1.
--   $$
--
--   The strict lower bound is the extra continuous-spectrum position assertion in the introduction; it is kept separate from the general observable range proposition.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 3, Unnumbered introduction result: strict spatial-index range and pure states

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

/-- Clark, PDF pp.3–4: strict spatial-index range, and its value on pure states.
The inherited nonzero-denominator domain is explicit, not totalized division.
Only position products are required; momentum regularity is not assumed. -/
theorem spatialIndex_strictRange {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d)) (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : ∀ j, RegularProduct (positionGraph j) rho)
    (hspread : coherenceSpread b positionGraph rho ≠ 0) :
    coherenceIndex b positionGraph rho ∈ Set.Ioc (0 : ℝ) 1 ∧
      ((∃ f : EuclideanSchrodinger d, ‖f‖ = (1 : ℝ) ∧
        rho = InnerProductSpace.rankOne ℂ f f) → coherenceIndex b positionGraph rho = 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
