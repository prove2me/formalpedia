-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P23_finiteMeasurementCorrespondence
-- name    : QAlgorithms.Papers.Independent.Renew46.P23.finiteMeasurementCorrespondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:32:32.745605+00:00
-- url     : https://prove2.me/theorems/6bf5089e-19c8-4f90-8a70-e02a24cdb59c
-- title:
--   Finite measurements and commutative coarse-grainings
-- statement:
--   Let $X$ be a finite nonempty set and let $N$ be a unital complex $C^*$-algebra. For a family $E:X\to N$, define the complex-linear map
--
--   $$\alpha_E(f)=\sum_{x\in X}f(x)E(x),\qquad f\in C(X).$$
--
--   The operators $E(x)$ are positive and sum to the identity if and only if $\alpha_E$ is a unital $2$-positive map. Conversely, every such map $\alpha:C(X)\to N$ is obtained this way, with $E(x)=\alpha(1_{\{x\}})$. This identifies finite measurements with coarse-grainings from a commutative algebra.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, PDF p. 3, Example 1: finite measurements are commutative-domain coarse-grainings

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- Example 1, PDF pp.3–4: finite measurements and commutative-domain
coarse-grainings correspond in both directions. Effects are recovered by
applying the map to the singleton indicator functions. Only 2-positivity
is requested; the codomain is an arbitrary unital C-star algebra. -/
theorem finiteMeasurementCorrespondence
    {X N : Type*} [Fintype X] [Nonempty X] [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] (E : X → N) :
    (((∀ x, 0 ≤ E x) ∧ (∑ x, E x) = 1) ↔
      IsCStarCoarseGraining (measurementMap E)) ∧
    (∀ sigma : (X → ℂ) →ₗ[ℂ] N, IsCStarCoarseGraining sigma →
      (∀ x, 0 ≤ sigma (fun y => if y = x then 1 else 0)) ∧
      (∑ x, sigma (fun y => if y = x then 1 else 0)) = 1 ∧
      sigma = measurementMap (fun x => sigma (fun y => if y = x then 1 else 0))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P23

end
