-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauF_sHom
-- name    : ReciprocityTheory.ChartRestriction.G.T0.tauF_sHom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:10.092573+00:00
-- url     : https://prove2.me/theorems/c570718a-70e5-43da-8f39-6c5c15dc5417
-- title:
--   T0: tau F s Hom
-- statement:
--   The T0 construction uses the tau F s Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L191-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L191-L222

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
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

theorem ReciprocityTheory.ChartRestriction.G.T0.tauF_sHom (b : Fin (D + 1)) (hb : b ≠ 0) (u : Kˣ) (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (F : MvPolynomial (TVar D N) K) :
    tauF b u (sHom j₀ x F) = sHom j₀ x (sigP b u F) := by sorry
