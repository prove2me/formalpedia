-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ker_eval_ne_bot
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ker_eval_ne_bot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:26.205069+00:00
-- url     : https://prove2.me/theorems/9bb321a4-9776-443f-a416-7f75559db118
-- title:
--   T0: ker eval ne bot
-- statement:
--   The T0 construction uses the ker eval ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L87-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L87-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.ker_eval_ne_bot (hΩ : Algebra.trdeg K Ω = D) (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    kerP (K := K) (D := D) j₀ x ≠ ⊥ := by sorry
