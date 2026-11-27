-- Prove2me | Theorems.Thm_PalomarZF207_henkin_model_of_not_provable_neg
-- name    : PalomarZF207.henkin_model_of_not_provable_neg
-- status  : Proved
-- author  : @fl-39
-- created : 2026-11-27T00:02:33.8918+00:00
-- url     : https://prove2.me/theorems/372df241-3f34-4030-ba32-587178df699d
-- title:
--   Henkin model existence for consistent closed extensions of ZF
-- statement:
--   For any closed sentence $\varphi$ in the language of `PalomarZF207`, if $\mathrm{ZF} \nvdash \neg\varphi$, then there exists a nonempty model $(V, E)$ of ZF in which $\varphi$ holds under every assignment $s : \mathbb{N} \to V$.
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine (Henkin completeness for first-order ZF)

import Definitions.Def_palomar_zf207_zf

namespace PalomarZF207
theorem henkin_model_of_not_provable_neg (φ : Formula) (hClosed : Closed φ) : ¬ Provable (Neg φ) → ∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E ∧ ∀ s : Nat → V, eval E φ s := by sorry
end PalomarZF207
