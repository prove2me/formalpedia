-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomogIdeal_map_relabel_iff_4f1c2e3f1d3b
-- name    : P2M_GroundTheory_Heights__Heights_isMultiHomogIdeal_map_relabel_iff_4f1c2e3f1d3b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:49.980002+00:00
-- url     : https://prove2.me/theorems/61a03f55-10df-5c9c-ba78-890f0c888197
-- title:
--   P2 M Ground Theory Heights  Heights is Multi Homog Ideal map relabel iff 4f1c2e3f1d3b: P2 M Ground Theory Heights  Heights is Multi Homog Ideal map relabel iff 4f1c2e3f1d3b
-- statement:
--   The P2 M Ground Theory Heights  Heights is Multi Homog Ideal map relabel iff 4f1c2e3f1d3b construction uses the P2 M Ground Theory Heights  Heights is Multi Homog Ideal map relabel iff 4f1c2e3f1d3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L240-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L240-L254

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

theorem P2M_GroundTheory_Heights__Heights_isMultiHomogIdeal_map_relabel_iff_4f1c2e3f1d3b (V : Ideal (MRing ι)) :
    IsMultiHomogIdeal (V.map (relabelRingEquiv ε h)) ↔ IsMultiHomogIdeal V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isMultiHomogIdeal_map_relabel_iff» := P2M_GroundTheory_Heights__Heights_isMultiHomogIdeal_map_relabel_iff_4f1c2e3f1d3b
