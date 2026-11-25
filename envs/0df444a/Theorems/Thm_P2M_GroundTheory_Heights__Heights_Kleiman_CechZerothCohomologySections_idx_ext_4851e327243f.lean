-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_idx_ext_4851e327243f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_idx_ext_4851e327243f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:42.250161+00:00
-- url     : https://prove2.me/theorems/89799d35-430c-4a7a-97f3-d9f2031600ff
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections idx ext 4851e327243f: P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections idx ext 4851e327243f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections idx ext 4851e327243f construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections idx ext 4851e327243f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_idx_ext_4851e327243f {U : Finset (Fin (N + 1))} {i : ℕ} {K K' : Cech.Idx U i} (h : K.1.1 = K'.1.1) :
    K = K' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechZerothCohomologySections».«idx_ext» := P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_idx_ext_4851e327243f
