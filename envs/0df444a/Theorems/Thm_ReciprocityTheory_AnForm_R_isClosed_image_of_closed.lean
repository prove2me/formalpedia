-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isClosed_image_of_closed
-- name    : ReciprocityTheory.AnForm.R.isClosed_image_of_closed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:49.714561+00:00
-- url     : https://prove2.me/theorems/d5be107b-2411-4a77-b945-151d04c54f2c
-- title:
--   R: is Closed image of closed
-- statement:
--   The R construction uses the is Closed image of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L87-L95

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

theorem ReciprocityTheory.AnForm.R.isClosed_image_of_closed {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t] (x : S)
    (hc : IsClosed ({x} : Set S)) : IsClosed ({g.base x} : Set T) := by sorry
