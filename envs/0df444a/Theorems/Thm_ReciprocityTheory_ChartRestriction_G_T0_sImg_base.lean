-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sImg_base
-- name    : ReciprocityTheory.ChartRestriction.G.T0.sImg_base
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:37.850739+00:00
-- url     : https://prove2.me/theorems/311049ca-6526-416c-b6f8-644bee6f6ad9
-- title:
--   T0: s Img base
-- statement:
--   The T0 construction uses the s Img base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L71-L78

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

theorem ReciprocityTheory.ChartRestriction.G.T0.sImg_base (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    sImg (Ω := Ω) j₀ x ((0 : Fin (D + 1)), j₀) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inl ())) := by sorry
