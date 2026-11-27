-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeff_evW_mem
-- name    : ReciprocityTheory.ChartRestriction.G.T0.coeff_evW_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:21.258774+00:00
-- url     : https://prove2.me/theorems/83dfa4fe-85b2-5e48-a649-1111522ca500
-- title:
--   T0: coeff ev W mem
-- statement:
--   The T0 construction uses the coeff ev W mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L99-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L99-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
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
variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}
variable (W : Submodule R B)

theorem ReciprocityTheory.ChartRestriction.G.T0.coeff_evW_mem (w : Fin (N + 1) → B) {n : ℕ} (Q : MvPolynomial (UXVar D N) R)
    (hx : XHom n Q) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    coeff β (evW w Q) ∈
      Submodule.span R (Set.range fun s : Fin n → Fin (N + 1) => ∏ k, w (s k)) := by sorry
