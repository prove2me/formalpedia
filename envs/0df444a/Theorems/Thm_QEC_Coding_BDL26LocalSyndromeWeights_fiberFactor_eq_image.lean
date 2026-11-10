-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberFactor_eq_image
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.fiberFactor_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:42:06.161116+00:00
-- url     : https://prove2.me/theorems/fd7a8fc1-470d-446b-a38b-467bf4ef7ed6
-- title:
--   BDL26 Local Syndrome Weights: fiber Factor eq image
-- statement:
--   Injectivity makes the extension-indexed sum an actual original-word SET sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L254-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L254-L264

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical

theorem QEC.Coding.BDL26LocalSyndromeWeights.fiberFactor_eq_image {C Label : Type*} [Fintype C]
    (owner : C → Label) (label : Label)
    (A : Finset (Word Bit {c : C // owner c = label})) (t : ℝ) :
    fiberFactor owner label A t =
      weightedFamily (A.image (fiberExtend owner label)) t := by sorry
