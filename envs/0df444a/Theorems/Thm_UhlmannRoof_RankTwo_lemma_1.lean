-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_lemma_1
-- name    : UhlmannRoof.RankTwo.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:20.949123+00:00
-- url     : https://prove2.me/theorems/96e8fd8a-fafe-49a1-8206-b450b24043f1
-- title:
--   Lemma 1, p. 5 — an optimal decomposition into between rank and rank squared distinct pure states
-- statement:
--   Let $\omega$ be a density operator of rank $r$. There is an optimal decomposition of $\omega$ into $m$ **different pure states** with positive coefficients, where
--   $$r\le m\le r^2.$$
--   Optimality means that the weighted sum of the pure states' diagonal entropies equals $R(\omega)$.
--
--   This bounds the finite number of distinct pure states needed to attain the convex roof.
--
--   **Formalization Note** The family of pure states is injective, so $m$ counts different states rather than slots that can repeat. No positive dimension assumption is added: a state already has trace one.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, p. 5, Lemma 1

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, Lemma 1, p. 5: an optimal pure-state decomposition with between
`rank ω` and `rank ω ^ 2` distinct summands. -/
theorem lemma_1 {d : ℕ} (ω : Mat d) (hω : IsState ω) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (ρ : Fin m → Mat d),
      IsOptimalDecomp ω p ρ ∧ Function.Injective ρ ∧
      ω.rank ≤ m ∧ m ≤ ω.rank ^ 2 := by sorry

end UhlmannRoof.RankTwo
