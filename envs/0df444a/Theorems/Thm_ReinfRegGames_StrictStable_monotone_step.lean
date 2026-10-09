-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_monotone_step
-- name    : ReinfRegGames.StrictStable.monotone_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:50.215973+00:00
-- url     : https://prove2.me/theorems/ed7192b9-31d4-42e8-b41f-acdef0ff4279
-- title:
--   Proof of Theorem 5.2, Part IV, pp. 23–24 — h*(y) − y_{α*} = max_x {Σ_{µ≠α*} x_µ z_µ − h(x)} is nondecreasing in the relative scores z_µ
-- statement:
--   Let $h$ be a penalty function on $\Delta=\Delta(B)$ with conjugate $h^*(y)=\max_{x\in\Delta}\{\langle y|x\rangle-h(x)\}$, and fix a vertex $\alpha^*\in B$. For a score vector $y$ write $z_\mu=y_\mu-y_{\alpha^*}$ ($\mu\neq\alpha^*$) for the relative scores. Then
--   $$h^*(y)-y_{\alpha^*}=\max_{x\in\Delta}\Big\{\sum_{\mu\neq\alpha^*}x_\mu z_\mu-h(x)\Big\},$$
--   and consequently, for two score vectors $y,y'$ with $z'_\mu<z_\mu$ for all $\mu\neq\alpha^*$,
--   $$h^*(y')-y'_{\alpha^*}\ \le\ h^*(y)-y_{\alpha^*}.$$
--
--   Since $F_h(e_{\alpha^*},y)=h(e_{\alpha^*})+h^*(y)-y_{\alpha^*}$, the Fenchel coupling to the vertex does not increase when every relative score decreases. In the proof of Theorem 5.2 this shows that an orbit started in $U^*_\varepsilon$ cannot leave it.
--
--   **Formalization Note** The page writes a strict inequality $h^*(y')-y'_{\alpha^*}<h^*(y)-y_{\alpha^*}$. For a nonsteep penalty this is false: when the maximizer is the vertex $e_{\alpha^*}$ itself (e.g. the quadratic penalty with every $z_\mu\le-1$), both sides equal $-h(e_{\alpha^*})$. The proof of Theorem 5.2 only needs the weak inequality (the first exit point has coupling exactly $\varepsilon K_{\min}/2$ by continuity, while the initial coupling is strictly smaller), so the weak inequality is stated. The maximum is written as a real `sSup` over the image of $\Delta$, attained for a penalty function.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 23–24, proof of Theorem 5.2, Part IV (the sentence "More rigorously, note that F_k(x*_k, y_k) = …")

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem monotone_step {B : Type*} [Fintype B] [DecidableEq B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (αstar : B) (y y' : B → ℝ) :
    ReinfRegGames.Extinction.conj h y - y αstar =
        sSup ((fun x => (∑ μ ∈ Finset.univ.erase αstar, x μ * (y μ - y αstar)) - h x) ''
          stdSimplex ℝ B) ∧
      ((∀ μ, μ ≠ αstar → y' μ - y' αstar < y μ - y αstar) →
        ReinfRegGames.Extinction.conj h y' - y' αstar ≤ ReinfRegGames.Extinction.conj h y - y αstar) := by sorry

end ReinfRegGames.StrictStable
