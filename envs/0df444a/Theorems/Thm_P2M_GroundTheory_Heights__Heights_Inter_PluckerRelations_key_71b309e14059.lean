-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_key_71b309e14059
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_key_71b309e14059
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:32.031956+00:00
-- url     : https://prove2.me/theorems/701ca101-f136-499d-a154-65b964290c29
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations key 71b309e14059: P2 M Ground Theory Heights  Heights Inter Plucker Relations key 71b309e14059
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations key 71b309e14059 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations key 71b309e14059 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L147-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L147-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_key_71b309e14059 (i : S.ι) (l : S.ν) (k m : S.κ) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base (d + 4)) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base (d + 4)) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ (d + 1) * (wedgeVal S k m * S.δ l)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«key» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_key_71b309e14059
