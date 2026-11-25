-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_comp
-- name    : ReciprocityTheory.AnForm.R.val_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:03.65304+00:00
-- url     : https://prove2.me/theorems/8dbae351-76e3-46ac-a130-12028f48f7ee
-- title:
--   R: val comp
-- statement:
--   The R construction uses the val comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L145-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L145-L166

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

theorem ReciprocityTheory.AnForm.R.val_comp {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T) (hg : g ≫ t = s)
    [LocallyOfFiniteType s] [LocallyOfFiniteType t] {U : T.Opens} {V : S.Opens} (hVU : V ≤ g ⁻¹ᵁ U)
    (f : Γ(T, U)) (x : S) (hx : x ∈ V) (hc : IsClosed ({x} : Set S)) :
    IsClosed ({g.base x} : Set T) ∧ val s (g.appLE U V hVU f) x hx = val t f (g.base x) (hVU hx) := by sorry
