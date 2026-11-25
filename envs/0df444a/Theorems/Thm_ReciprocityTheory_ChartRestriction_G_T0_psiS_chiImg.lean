-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psiS_chiImg
-- name    : ReciprocityTheory.ChartRestriction.G.T0.psiS_chiImg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:42.811503+00:00
-- url     : https://prove2.me/theorems/c46211fb-b463-44bc-93c6-9fed7a08236a
-- title:
--   T0: psi S chi Img
-- statement:
--   The T0 construction uses the psi S chi Img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L33-L60

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

theorem ReciprocityTheory.ChartRestriction.G.T0.psiS_chiImg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (v : TVar D N)
    (hv : ¬ (v.1 = 0 ∧ v.2 = j₀)) :
    psiS (chiImg j₀ x v) = sImg (Ω := Ω) j₀ x v := by sorry
