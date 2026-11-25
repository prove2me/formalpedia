-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_pushout_quot
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.pushout_quot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:07.986389+00:00
-- url     : https://prove2.me/theorems/e114ac94-cb95-59cd-844e-e592d8f4a318
-- title:
--   TG: pushout quot
-- statement:
--   The TG construction uses the pushout quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L9-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean#L9-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.pushout_quot {R A B P : CommRingCat.{0}} {a : R ⟶ A} {b : R ⟶ B} {c : A ⟶ P} {d : B ⟶ P}
    (h : IsPushout a b c d) (hb : Function.Surjective b) :
    Function.Surjective c ∧ ∀ x, c x = 0 → x ∈ (RingHom.ker b.hom).map a.hom := by sorry
