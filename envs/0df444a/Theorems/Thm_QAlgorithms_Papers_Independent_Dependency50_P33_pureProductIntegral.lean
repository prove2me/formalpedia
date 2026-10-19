-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P33_pureProductIntegral
-- name    : QAlgorithms.Papers.Independent.Dependency50.P33.pureProductIntegral
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:20:47.764659+00:00
-- url     : https://prove2.me/theorems/cc168e38-f016-485d-93cb-3d51015e9ec6
-- title:
--   Pure-product closure and integral characterization of separability
-- statement:
--   Let $H$ and $K$ be nonzero separable complex Hilbert spaces, and let $\mathfrak P(H)$ and $\mathfrak P(K)$ denote their pure density operators, with the inherited trace-norm Borel structures. For every density operator $\rho$ on the completed tensor product $H\otimes K$, the following are equivalent:
--
--   $$
--   \begin{aligned}
--   &\rho\text{ is separable};\\
--   &\rho\in\overline{\operatorname{co}}\{\alpha\otimes\beta:\alpha\in\mathfrak P(H),\ \beta\in\mathfrak P(K)\};\\
--   &\rho=\int_{\mathfrak P(H)\times\mathfrak P(K)}\alpha\otimes\beta\,\nu(d\alpha,d\beta)
--   \quad\text{for some Borel probability measure }\nu.
--   \end{aligned}
--   $$
--
--   The closure is in trace norm and the integral is the trace-class Bochner integral. Pure states are density operators rather than chosen vector representatives. In particular, no measurable choice of global phases and no atomicity assumption is made.
--
--   This representation permits pure-product continuous ensembles for all separable states. Although p.3 says Borel measure, trace one forces its total mass to be one, and p.5 explicitly describes it as a probability measure.
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, PDF p. 3, §2, equation (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.RealRegisters (Hilbert)

/-- Pure-product replacement in Definition 1 and integral (4), PDF p.3.
The probability law is on pure density operators, with no chosen vector phases. -/
theorem pureProductIntegral {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (rho : State (I × J)) :
    (IsSeparable rho.coefficients ↔
      rho.coefficients ∈ traceClosure (convexHull ℝ
        {X | ∃ (a : PureState I) (b : PureState J),
          X = productCoeff a.val.coefficients b.val.coefficients})) ∧
    (IsSeparable rho.coefficients ↔
      ∃ mu : Measure (PureState I × PureState J), IsProbabilityMeasure mu ∧
        IsBarycenter mu
          (fun p => productCoeff p.1.val.coefficients p.2.val.coefficients)
          rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P33

end
