-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subst_C_mul_ps
-- name    : ReciprocityTheory.ChartRestriction.L1.subst_C_mul_ps
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:25.585903+00:00
-- url     : https://prove2.me/theorems/7680d23d-4be0-5114-a11d-68ce7a1ec72e
-- title:
--   L1: subst C mul ps
-- statement:
--   The L1 construction uses the subst C mul ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L41-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.L1.subst_C_mul_ps {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by sorry
