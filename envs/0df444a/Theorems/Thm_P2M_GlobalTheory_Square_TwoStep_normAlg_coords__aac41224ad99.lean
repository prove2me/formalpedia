-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99
-- name    : P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:35.508387+00:00
-- url     : https://prove2.me/theorems/b8f9abe7-ae02-46d4-95ff-60cb0e83a551
-- title:
--   P2 M Global Theory Square Two Step norm Alg coords  aac41224ad99: P2 M Global Theory Square Two Step norm Alg coords  aac41224ad99
-- statement:
--   The P2 M Global Theory Square Two Step norm Alg coords  aac41224ad99 construction uses the P2 M Global Theory Square Two Step norm Alg coords  aac41224ad99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L264-L266

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep

theorem P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99 (t : ℕ) : normAlg (square K).G (coords K t).gam (coords K t).z' = 1 := by sorry

alias «GlobalTheory».«Square».«TwoStep».«normAlg_coords'» := P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99
