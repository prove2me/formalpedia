-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_transpose_tannerBoundary_smallSetExpandingAtRelativeRadius_of_dualExposed
-- name    : QEC.Coding.BalancedProduct.LPSTanner.transpose_tannerBoundary_smallSetExpandingAtRelativeRadius_of_dualExposed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:20.17771+00:00
-- url     : https://prove2.me/theorems/6f87a412-46e7-4c89-8661-65c0f7de007b
-- title:
--   LPSTanner: transpose tanner Boundary small Set Expanding At Relative Radius of dual Exposed
-- statement:
--   Dual aggregation interface parallel to the primal one.  A graph-side
--   lower bound on exposed supported vertices implies exact small-set expansion
--   of the actual global transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L887-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L887-L909

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

theorem QEC.Coding.BalancedProduct.LPSTanner.transpose_tannerBoundary_smallSetExpandingAtRelativeRadius_of_dualExposed
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : ℕ)
    (hradius : 0 < radiusDenominator)
    (hexpansion : 0 < expansionDenominator)
    (hexposed : ∀ y : Word (ZMod 2) (Check401 q),
      radiusDenominator * HammingWeight y ≤
          radiusNumerator * Fintype.card (Check401 q) →
      expansionNumerator * HammingWeight y ≤
        expansionDenominator *
          (dualExposedVertices q hq40 hq y).card) :
    (wordLinearMapTranspose
      (tannerBoundary q hq40 hq)).SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator := by sorry
