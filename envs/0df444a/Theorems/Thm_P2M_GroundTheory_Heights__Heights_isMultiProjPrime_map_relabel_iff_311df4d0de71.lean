-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiProjPrime_map_relabel_iff_311df4d0de71
-- name    : P2M_GroundTheory_Heights__Heights_isMultiProjPrime_map_relabel_iff_311df4d0de71
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:00.863907+00:00
-- url     : https://prove2.me/theorems/ee6dcec7-d280-498d-8cfc-c0c4f565b6b9
-- title:
--   P2 M Ground Theory Heights  Heights is Multi Proj Prime map relabel iff 311df4d0de71: P2 M Ground Theory Heights  Heights is Multi Proj Prime map relabel iff 311df4d0de71
-- statement:
--   The P2 M Ground Theory Heights  Heights is Multi Proj Prime map relabel iff 311df4d0de71 construction uses the P2 M Ground Theory Heights  Heights is Multi Proj Prime map relabel iff 311df4d0de71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L256-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L256-L259

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

theorem P2M_GroundTheory_Heights__Heights_isMultiProjPrime_map_relabel_iff_311df4d0de71 (V : Ideal (MRing ι)) :
    IsMultiProjPrime (V.map (relabelRingEquiv ε h)) ↔ IsMultiProjPrime V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isMultiProjPrime_map_relabel_iff» := P2M_GroundTheory_Heights__Heights_isMultiProjPrime_map_relabel_iff_311df4d0de71
