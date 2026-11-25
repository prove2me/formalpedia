-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_charOf_map_relabel_ff9c6d4a87db
-- name    : P2M_GroundTheory_Heights__Heights_charOf_map_relabel_ff9c6d4a87db
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:30.655909+00:00
-- url     : https://prove2.me/theorems/846d8e44-07fc-54f9-975f-1bcf3d2108c1
-- title:
--   P2 M Ground Theory Heights  Heights char Of map relabel ff9c6d4a87db: P2 M Ground Theory Heights  Heights char Of map relabel ff9c6d4a87db
-- statement:
--   The P2 M Ground Theory Heights  Heights char Of map relabel ff9c6d4a87db construction uses the P2 M Ground Theory Heights  Heights char Of map relabel ff9c6d4a87db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L261-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L261-L268

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

theorem P2M_GroundTheory_Heights__Heights_charOf_map_relabel_ff9c6d4a87db (V : Ideal (MRing ι)) :
    charOf (V.map (relabelRingEquiv ε h)) = charOf V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«charOf_map_relabel» := P2M_GroundTheory_Heights__Heights_charOf_map_relabel_ff9c6d4a87db
