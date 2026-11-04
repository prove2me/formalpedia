-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_factor_physical
-- name    : ThreeSum.TernarySourceHostModel.factor_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:48.592165+00:00
-- url     : https://prove2.me/theorems/e3339f05-e663-44fa-a0a4-89b8e147db2d
-- title:
--   Ternary Source Host Model: factor physical
-- statement:
--   A source-type constant factorial is the pointwise factorial weighting
--   required by the exact convolution theorem.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L138-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L138-L153

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}

theorem ThreeSum.TernarySourceHostModel.factor_physical (S : Finset (ℕ × ℕ)) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (factor : ℤ)
    (hfactor : ∀ pair∈S, factor=TernaryConvolution.factorial (enumeration (key pair.2)))
    (g : ℕ) (R : TritWord N) :
    factor*physical S enumeration key group weight g R=
      TernaryConvolution.factorial R*physical S enumeration key group weight g R := by sorry
