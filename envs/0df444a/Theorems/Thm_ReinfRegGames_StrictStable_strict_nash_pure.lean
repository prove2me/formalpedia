-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_strict_nash_pure
-- name    : ReinfRegGames.StrictStable.strict_nash_pure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:30.859978+00:00
-- url     : https://prove2.me/theorems/6ab7b635-359f-4c22-9618-8efd5d31c81b
-- title:
--   Proof of Theorem 5.2, Part IV, p. 23 — a strict equilibrium is a pure profile (α*_1, …, α*_N) with δ_k = min_µ {v_{kα*}(x*) − v_{kµ}(x*)} > 0
-- statement:
--   Let $\mathcal G$ be a finite game with a finite set $\mathcal N$ of players; player $k$ has a finite set $\mathcal A_k$ of pure strategies and payoff function $u_k:\prod_\ell \mathcal A_\ell\to\mathbb R$. A mixed profile $x=(x_1,\dots,x_N)$ is an element of $\mathcal X=\prod_k\Delta(\mathcal A_k)$, and $u_k(x)$ is player $k$'s expected payoff (2.1) when the players randomize independently. $v_{k\alpha}(x)=u_k(\alpha;x_{-k})$ is the payoff of the pure strategy $\alpha\in\mathcal A_k$ against $x_{-k}$ (2.2).
--
--   Let $x^*$ be a strict Nash equilibrium of $\mathcal G$. Then for every player $k$ there is a pure strategy $\alpha_k^*\in\mathcal A_k$ with $x^*_k=e_{\alpha^*_k}$ (the vertex of $\Delta(\mathcal A_k)$ at $\alpha^*_k$), and
--   $$v_{k\mu}(x^*)<v_{k\alpha^*_k}(x^*)\qquad\text{for every }\mu\in\mathcal A_k\setminus\{\alpha^*_k\},$$
--   so that $\delta_k=\min_{\mu\neq\alpha^*_k}\{v_{k\alpha^*_k}(x^*)-v_{k\mu}(x^*)\}>0$.
--
--   The proof of Part IV of Theorem 5.2 starts by writing $x^*=(\alpha^*_1,\dots,\alpha^*_N)$ and uses the positive gaps $\delta_k$ to show that the relative scores $z_{k\mu}=y_{k\mu}-y_{k\alpha^*_k}$ decrease linearly near $x^*$.
--
--   **Formalization Note** The page asserts both facts in passing ("let $x^*=(\alpha^*_1,\dots,\alpha^*_N)$ be a strict equilibrium", "$\delta_k=\dots>0$"); here they are stated as a lemma about the definition of strict equilibrium, which does not build purity in. The minimum over $\mathcal A_k\setminus\{\alpha^*_k\}$ is stated as a strict inequality for every $\mu\ne\alpha^*_k$, which is equivalent on a finite set and avoids an empty minimum when $|\mathcal A_k|=1$.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 23, proof of Theorem 5.2, Part IV ("let x* = (α*_1, …, α*_N) be a strict equilibrium", "δ_k = min … > 0")

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_StrictStable_Stability

namespace ReinfRegGames.StrictStable

theorem strict_nash_pure {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ)
    (xstar : ∀ k, A k → ℝ) (hstrict : IsStrictNash u xstar) :
    ∀ k, ∃ αstar : A k, xstar k = Pi.single αstar 1 ∧
      ∀ μ : A k, μ ≠ αstar → ReinfRegGames.Extinction.payoffVec u xstar k μ < ReinfRegGames.Extinction.payoffVec u xstar k αstar := by sorry

end ReinfRegGames.StrictStable
