-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasMeanZeroComplexOperatorBound_rightCayleyGraph_iff
-- name    : QEC.Coding.TannerLiftedProduct.hasMeanZeroComplexOperatorBound_rightCayleyGraph_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:24:35.869084+00:00
-- url     : https://prove2.me/theorems/844c999b-5142-4ddc-851a-be2e5db35c4a
-- title:
--   Tanner Lifted Product: has Mean Zero Complex Operator Bound right Cayley Graph iff
-- statement:
--   Direct right-regular-action formulation of the complex mean-zero
--   operator bound on a labelled Cayley multigraph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L327-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L327-L336

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.hasMeanZeroComplexOperatorBound_rightCayleyGraph_iff
    (label : W → G) (spectral : ℝ) :
    SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph label) spectral ↔
      ∀ f : G → ℂ,
        (∑ g, f g) = 0 →
          (∑ g, ‖cayleyRightTranslationSum label f g‖ ^ 2) ≤
            spectral ^ 2 * ∑ g, ‖f g‖ ^ 2 := by sorry
