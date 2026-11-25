-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psiS_chiImg_base
-- name    : ReciprocityTheory.ChartRestriction.G.T0.psiS_chiImg_base
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:47.078299+00:00
-- url     : https://prove2.me/theorems/7a0c2d36-9968-5b0c-a456-cfd0861f06f4
-- title:
--   T0: psi S chi Img base
-- statement:
--   The T0 construction uses the psi S chi Img base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L62-L69

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

theorem ReciprocityTheory.ChartRestriction.G.T0.psiS_chiImg_base (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    psiS (chiImg j₀ x ((0 : Fin (D + 1)), j₀)) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr ((0 : Fin (D + 1)), k)) * C (x k)) := by sorry
