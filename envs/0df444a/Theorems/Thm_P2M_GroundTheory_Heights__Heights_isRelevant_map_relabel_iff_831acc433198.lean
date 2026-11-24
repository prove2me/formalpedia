-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198
-- name    : P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:13.690782+00:00
-- url     : https://prove2.me/theorems/397886de-1166-4bf4-9404-741ced063f74
-- title:
--   P2 M Ground Theory Heights  Heights is Relevant map relabel iff 831acc433198: P2 M Ground Theory Heights  Heights is Relevant map relabel iff 831acc433198
-- statement:
--   The P2 M Ground Theory Heights  Heights is Relevant map relabel iff 831acc433198 construction uses the P2 M Ground Theory Heights  Heights is Relevant map relabel iff 831acc433198 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L200-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L200-L211

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198 (V : Ideal (MRing ι)) :
    IsRelevant (V.map (relabelRingEquiv ε h)) ↔ IsRelevant V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isRelevant_map_relabel_iff» := P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198
