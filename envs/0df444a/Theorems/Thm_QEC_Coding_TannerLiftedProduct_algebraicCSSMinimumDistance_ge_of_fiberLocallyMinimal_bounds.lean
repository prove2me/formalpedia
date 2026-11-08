-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
-- name    : QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:49:35.429516+00:00
-- url     : https://prove2.me/theorems/9de619cd-0972-4b79-9e5e-9006ca94683a
-- title:
--   Tanner Lifted Product: algebraic CSSMinimum Distance ge of fiber Locally Minimal bounds
-- statement:
--   Primal and dual local-minimal bounds for the source-level coefficient
--   fibers imply the same lower bound on the attained algebraic CSS minimum
--   distance. This is the local-minimality interface used by the PK22 proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1688-L1730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1688-L1730

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (lowerBound d : Nat)
    (hcycles : ∀ c,
      c ∈ (chainComplex label h g').middleCycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (horizontalFiberBoundaryMoves label h g') c →
      lowerBound ≤ blockWeight c)
    (hcocycles : ∀ c,
      c ∈ (chainComplex label h g').middleCocycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (verticalFiberCoboundaryMoves label h g') c →
      lowerBound ≤ blockWeight c)
    (hminimum : AlgebraicCSSMinimumDistance
      (chainComplex label h g').firstCoboundaryCheckCode
      (chainComplex label h g').middleBoundaryCode d) :
    lowerBound ≤ d := by sorry
