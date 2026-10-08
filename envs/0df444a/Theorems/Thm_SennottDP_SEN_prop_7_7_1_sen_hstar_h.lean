-- Prove2me | Theorems.Thm_SennottDP_SEN_prop_7_7_1_sen_hstar_h
-- name    : SennottDP.SEN.prop_7_7_1_sen_hstar_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:29:21.97598+00:00
-- url     : https://prove2.me/theorems/fd5f1296-b20d-4361-a4f2-e3896ba7f581
-- title:
--   Proposition 7.7.1 — (SEN) implies (H*), and (H*) implies (H)
-- statement:
--   Let $z$ be a distinguished state. The three assumption sets are nested:
--
--   $$\text{(SEN)} \;\Longrightarrow\; \text{(H}^*\text{)} \;\Longrightarrow\; \text{(H)}.$$
--
--   Precisely: if (SEN) holds with the function $M$ in (SEN2) and the constant $L$ in (SEN3), then (H\*) holds with the same $M$ and the constant function $L(\cdot) \equiv L$; and if (H\*) holds with functions $M$ and $L$, then (H) holds with the same $M$ and $L$.
--
--   The (H) assumptions weaken (SEN3) by allowing the lower bound on $h_\alpha$ to be a function, at the price of the integrability conditions (H4)–(H5); (H\*5) is a sufficient condition for (H5) that is easier to check.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 158, Proposition 7.7.1

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.7.1, p. 158: (SEN) ⇒ (H*) ⇒ (H). With the witnesses made
explicit: if (SEN) holds for `z` with function `Mf` and constant `L`, then (H*) holds for `z`
with `Mf` and the constant function `L(·) = L`; and if (H*) holds for `z` with functions `Mf`,
`Lf`, then (H) holds for `z` with the same `Mf`, `Lf`. -/
theorem prop_7_7_1_sen_hstar_h {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ (Mf : S → ℝ) (L : ℝ), SENAssumptions M z Mf L → HStarAssumptions M z Mf (fun _ => L)) ∧
      ∀ Mf Lf : S → ℝ, HStarAssumptions M z Mf Lf → HAssumptions M z Mf Lf := by sorry

end SennottDP.SEN
