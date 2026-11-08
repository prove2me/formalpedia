-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_smallSetExpandingAtRelativeRadius_of_activeLightVertices
-- name    : QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_smallSetExpandingAtRelativeRadius_of_activeLightVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:17.535281+00:00
-- url     : https://prove2.me/theorems/a330082c-a968-4e28-9097-69d04a468f64
-- title:
--   LPSTanner: tanner Boundary small Set Expanding At Relative Radius of active Light Vertices
-- statement:
--   Pure combinatorial aggregation interface.  Once graph expansion proves
--   that every relatively small support has sufficiently many active light
--   vertices, the concrete Tanner boundary satisfies the project's exact
--   small-set-expansion predicate.  The premise mentions no syndrome conclusion
--   and is discharged later from the LPS spectral estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L608-L629
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L608-L629

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype

theorem QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_smallSetExpandingAtRelativeRadius_of_activeLightVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : ℕ)
    (hradius : 0 < radiusDenominator)
    (hexpansion : 0 < expansionDenominator)
    (hactive : ∀ x : Word (ZMod 2) (Edge401 q hq),
      radiusDenominator * HammingWeight x ≤
          radiusNumerator * Fintype.card (Edge401 q hq) →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator *
          (activeLightVertices q hq40 hq x).card) :
    (tannerBoundary q hq40 hq).SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator := by sorry
