-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:59.192791+00:00
-- url     : https://prove2.me/theorems/23edf5e0-46e8-4c78-ba1f-0056b1d7942e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers split Frac Map mk 90d3ee9fcc29: P2 M Ground Theory Heights  Heights Field Numbers split Frac Map mk 90d3ee9fcc29
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers split Frac Map mk 90d3ee9fcc29 construction uses the P2 M Ground Theory Heights  Heights Field Numbers split Frac Map mk 90d3ee9fcc29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L32-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29 (f : MRing (splitCoord j ι') F) :
    splitFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (splitPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (splitVar j ι') f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«splitFracMap_mk» := P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29
