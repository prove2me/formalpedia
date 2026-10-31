-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_gapNPHard_of_reduction
-- name    : SetCoverThreshold.SetCover.gapNPHard_of_reduction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T19:42:49.493768+00:00
-- url     : https://prove2.me/theorems/15a70bda-0fe7-48da-9b13-cfc1c61fb0d3
-- title:
--   Gap NP-hardness preserved under polynomial-time gap-preserving reductions
-- statement:
--   Gap NP-hardness is preserved under polynomial-time gap-preserving reductions. If a promise problem $(Yes_1, No_1)$ with encoding $\mathrm{enc}_1$ is gap NP-hard, and $(g, g_{\mathrm{enc}})$ is a polynomial-time reduction mapping $Yes_1$ instances to $Yes_2$ instances and $No_1$ instances to $No_2$ instances under encoding $\mathrm{enc}_2$, then $(Yes_2, No_2)$ is also gap NP-hard under $\mathrm{enc}_2$.
-- source:
--   Feige 1998, A Threshold of ln n for Approximating Set Cover, J. ACM 45(4): 634–652, Section 2

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

namespace SetCoverThreshold.SetCover

/-- Gap NP-hardness is preserved under polynomial-time gap-preserving reductions. -/
theorem gapNPHard_of_reduction {α β Sym₁ Sym₂ : Type}
    (enc₁ : α → List Sym₁) (Yes₁ No₁ : α → Prop)
    (enc₂ : β → List Sym₂) (Yes₂ No₂ : β → Prop)
    (h₁ : GapNPHard enc₁ Yes₁ No₁)
    (g : α → β) (g_enc : List Sym₁ → List Sym₂)
    (hg_poly : CookPvsNP.PolyTimeComputable g_enc)
    (hg_enc : ∀ a, (Yes₁ a ∨ No₁ a) → enc₂ (g a) = g_enc (enc₁ a))
    (hg_yes : ∀ a, Yes₁ a → Yes₂ (g a))
    (hg_no : ∀ a, No₁ a → No₂ (g a)) :
    GapNPHard enc₂ Yes₂ No₂ := by
  sorry

end SetCoverThreshold.SetCover
