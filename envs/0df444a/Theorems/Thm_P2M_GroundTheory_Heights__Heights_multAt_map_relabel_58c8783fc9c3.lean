-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_multAt_map_relabel_58c8783fc9c3
-- name    : P2M_GroundTheory_Heights__Heights_multAt_map_relabel_58c8783fc9c3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:22.757+00:00
-- url     : https://prove2.me/theorems/36f5cc64-cb3a-4da1-9474-2e6e1c6e6785
-- title:
--   P2 M Ground Theory Heights  Heights mult At map relabel 58c8783fc9c3: P2 M Ground Theory Heights  Heights mult At map relabel 58c8783fc9c3
-- statement:
--   The P2 M Ground Theory Heights  Heights mult At map relabel 58c8783fc9c3 construction uses the P2 M Ground Theory Heights  Heights mult At map relabel 58c8783fc9c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L284-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L284-L294

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

theorem P2M_GroundTheory_Heights__Heights_multAt_map_relabel_58c8783fc9c3 (J V : Ideal (MRing ι)) :
    multAt (J.map (relabelRingEquiv ε h)) (V.map (relabelRingEquiv ε h)) = multAt J V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«multAt_map_relabel» := P2M_GroundTheory_Heights__Heights_multAt_map_relabel_58c8783fc9c3
