-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_aeval_scale_rows
-- name    : ReciprocityTheory.ChartRestriction.G.T0.aeval_scale_rows
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:05.048193+00:00
-- url     : https://prove2.me/theorems/6ccc66e0-1ffc-5454-9a97-68270c528a3a
-- title:
--   T0: aeval scale rows
-- statement:
--   The T0 construction uses the aeval scale rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PowFirstVarDvdSubstitution.lean#L8-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PowFirstVarDvdSubstitution.lean#L8-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.aeval_scale_rows {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by sorry
