-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_theorem_5_2_iv
-- name    : ReinfRegGames.StrictStable.theorem_5_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:00.092987+00:00
-- url     : https://prove2.me/theorems/95a8c6f3-0308-4246-9512-4c8f06298b3e
-- title:
--   Theorem 5.2, Part IV, p. 22 — under (RL), every strict Nash equilibrium is asymptotically stable
-- statement:
--   Let $\mathcal G$ be a finite game with a finite set $\mathcal N$ of players; player $k$ has a finite set $\mathcal A_k$ of pure strategies and payoff function $u_k:\prod_\ell \mathcal A_\ell\to\mathbb R$. A mixed profile $x=(x_1,\dots,x_N)$ is an element of $\mathcal X=\prod_k\Delta(\mathcal A_k)$, and $u_k(x)$ is player $k$'s expected payoff (2.1) when the players randomize independently. $v_{k\alpha}(x)=u_k(\alpha;x_{-k})$ is the payoff of the pure strategy $\alpha\in\mathcal A_k$ against $x_{-k}$ (2.2). Every player $k$ has a penalty function $h_k$ on $\Delta(\mathcal A_k)$ in the sense of Definition 2.1 (continuous on the simplex, smooth on the relative interior of every face, $K_k$-strongly convex), with choice map $Q_k(y_k)=\arg\max_{x_k\in\Delta(\mathcal A_k)}\{\langle y_k|x_k\rangle-h_k(x_k)\}$ (2.8). An orbit of (RL) is a pair of trajectories $y(t)$, $x(t)=Q(y(t))$, $t\ge0$, with $\dot y_{k\alpha}=v_{k\alpha}(x)$.
--
--   **Theorem (Part IV).** If $x^*$ is a strict Nash equilibrium of $\mathcal G$, then $x^*$ is asymptotically stable under (RL): it is Lyapunov stable — for every $\varepsilon>0$ there is $\delta>0$ such that every orbit with $\|x(0)-x^*\|<\delta$ satisfies $\|x(t)-x^*\|<\varepsilon$ for all $t\ge0$ — and attracting — there is $\delta>0$ such that every orbit with $\|x(0)-x^*\|<\delta$ satisfies
--   $$\lim_{t\to\infty}x(t)=x^*.$$
--
--   This is the regularized-learning analogue of the classical fact that strict equilibria are asymptotically stable under the replicator dynamics. It holds for every choice of penalty functions, steep or not; in the steep case $x^*$ is never reached, while in the nonsteep case (e.g. the projection dynamics) it may be reached in finite time.
--
--   **Formalization Note** The norm in the strong convexity inequality (2.5) is the Euclidean one; the page leaves it unspecified, and since $K$ is existential in Definition 2.1 the class of penalty functions does not depend on this choice, but the constant $K$ does. (RL) is encoded in its differential form (3.1): $x_k(t)$ maximizes $\langle y_k(t)|\cdot\rangle-h_k$ over the simplex and $y_{k\alpha}$ has right derivative $v_{k\alpha}(x(t))$ at every $t\ge0$ (one-sided at $t=0$); since $x=Q(y)$ is continuous along an orbit, this is equivalent to the integral form (RL) on p. 7. Neighbourhoods of $x^*$ in $\mathcal X$ are encoded by balls of the sup metric on $\prod_k\mathbb R^{\mathcal A_k}$; every $x(t)$ lies in $\mathcal X$, so these balls intersected with $\mathcal X$ are exactly the relative neighbourhoods, and the "for every neighbourhood $U$ there is a neighbourhood $V$" of Definition 5.1 is the equivalent $\varepsilon$–$\delta$ form. No steepness, no decomposability and no assumption $x^*\in\operatorname{im}Q$ is made (the latter appears only in Part I).
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 22, Theorem 5.2, Part IV (proof pp. 23–24); Definition 5.1, p. 21

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_StrictStable_Stability

namespace ReinfRegGames.StrictStable

theorem theorem_5_2_iv {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (xstar : ∀ k, A k → ℝ) (hstrict : IsStrictNash u xstar) :
    IsAsymptoticallyStable u h xstar := by sorry

end ReinfRegGames.StrictStable
