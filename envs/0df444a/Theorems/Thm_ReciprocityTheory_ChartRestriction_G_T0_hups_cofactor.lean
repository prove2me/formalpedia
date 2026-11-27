-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_cofactor
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_cofactor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T06:07:08.745871+00:00
-- url     : https://prove2.me/theorems/f5ed8f38-0b29-523e-ad62-c2061fee67b5
-- title:
--   T0: hups cofactor
-- statement:
--   The T0 construction uses the hups cofactor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L30-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_cofactor {R : Type*} [CommRing R] [IsDomain R] {D N : ℕ}
    {F P : MvPolynomial (UXVar D N) R} (hF : F ≠ 0) {deF u n n' : ℕ} (hFx : XHom deF F)
    {sF : UXVar D N →₀ ℕ} (hsF : sF ∈ F.support) (hsFu : uDeg sF = u)
    (hx : XHom n (F * P)) (hu : UDegLE n' (F * P)) :
    ∀ s ∈ P.support, s ∈ upMono D N (n - deF) (n' - u) := by sorry
