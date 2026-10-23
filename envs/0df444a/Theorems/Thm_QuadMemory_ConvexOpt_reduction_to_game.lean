-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_reduction_to_game
-- name    : QuadMemory.ConvexOpt.reduction_to_game
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:02.594981+00:00
-- url     : https://prove2.me/theorems/086fdf01-8163-4afb-990c-4bd564dab4ce
-- title:
--   Proof of Theorem 1, p. 25 — an M-bit algorithm solving convex optimization to 1/d⁴ within Q queries gives a Game 2 strategy with m = ⌈Q/p_max⌉ + 1
-- statement:
--   There is a universal constant $C'>0$ such that the following holds. Let $1\le k\le d/3-1$ with $p_{max}\ge1$, and let $\mathcal D_\delta$ be a discretization of the sphere whose cells have diameter at most $1/d^3$. Let $alg$ be an $M$-bit deterministic first-order algorithm that minimizes every $1$-Lipschitz convex function over $B_d(0,1)$ to accuracy $\epsilon=1/d^4$ with at most $Q$ queries, where $\lceil Q/p_{max}\rceil+1\le d$. Then there is a strategy for Game 2 with parameters
--   $$\Big(d,\ k,\ \Big\lceil\frac Q{p_{max}}\Big\rceil+1,\ M,\ \alpha=\frac{2\eta}{\gamma_1},\ \beta=\frac{\gamma_2}4\Big)$$
--   in which the Player wins with probability at least $1-C'\sqrt{\log d}/d$.
--
--   This is the bridge from the convex optimization model to the game: Proposition 8 (with the $\sqrt d$-Lipschitz rescaling of $F_{A,v,P,L}$) makes the algorithm successful for the procedure, and Proposition 11 converts it into a Game 2 strategy. Combined with Proposition 14 it gives Theorem 1.
--
--   **Formalization Note.** The statement mentions only the convex optimization model, Game 2 and the parameters $\eta,\gamma_1,\gamma_2,p_{max}$. The hypotheses $p_{max}\ge1$ and $\lceil Q/p_{max}\rceil+1\le d$ are the ones Propositions 10 and 11 need ($m\le d$, at most $d^2$ queries), which the proof of Theorem 1 uses silently; when they fail, Theorem 1's conclusion holds for other reasons.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 25, Proof of Theorem 1 (reduction step)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

namespace QuadMemory.ConvexOpt

/-- Proof of Theorem 1, p. 25 (the reduction): there is a universal `C' > 0` such that, for
`1 ≤ k ≤ d/3 - 1` with `p_max ≥ 1`, any discretization `D` of the sphere into cells of diameter
at most `1/d³`, and any `M`-bit algorithm that minimizes `1`-Lipschitz convex functions over the
unit ball to accuracy `1/d⁴` with at most `Q` queries, where `⌈Q/p_max⌉ + 1 ≤ d`, there is a
strategy for Game 2 with parameters `(d, k, ⌈Q/p_max⌉ + 1, M, α = 2η/γ₁, β = γ₂/4)` that wins with
probability at least `1 - C' √(log d)/d`. -/
theorem reduction_to_game :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (d k M Q : ℕ), 1 ≤ k → (k : ℝ) ≤ (d : ℝ) / 3 - 1 → 1 ≤ pmax d k →
      ⌈(Q : ℝ) / pmax d k⌉₊ + 1 ≤ d →
      ∀ (D : SphereDisc d), D.DiamLe (1 / (d : ℝ) ^ 3) →
      ∀ (alg : MemAlg d M), SolvesCO alg Q (1 / (d : ℝ) ^ 4) →
      ∃ P : Player d k (⌈(Q : ℝ) / pmax d k⌉₊ + 1) M D,
        ENNReal.ofReal (1 - C' * Real.sqrt (Real.log d) / d) ≤
          winProb P (2 * eta d / gamma1 d) (gamma2 d / 4) := by sorry

end QuadMemory.ConvexOpt
