-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_theorem7
-- name    : SongZipkinFluct.Monotone.theorem7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:15.279842+00:00
-- url     : https://prove2.me/theorems/b133d311-4b93-497e-89c8-7a76b90a46bd
-- title:
--   Theorem 7 — ΔW_{n−1} and ΔG_n are nonincreasing and y*_n is nondecreasing in the world state
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 and Condition 1 for a partial order $\preceq$ on the world states. Consider the linear-cost model, $K = 0$, with terminal cost $W_0 \equiv 0$, and its recursion
--   $$G_n(i,y) = G^+(i,y) + \beta\lambda_i c + \beta\Big\{\lambda_i W_{n-1}(i,y-1) + \sum_{j\ne i} q_{ij}W_{n-1}(j,y) + (\mu-\lambda_i-q_i)W_{n-1}(i,y)\Big\},\quad W_n(i,x) = \min_{y\ge x} G_n(i,y).$$
--   Then for all $n \ge 1$ and every fixed integer $x$:
--
--   1. $\Delta W_{n-1}(i,x)$ is nonincreasing in $i$;
--   2. $\Delta G_n(i,x)$ is nonincreasing in $i$;
--   3. the smallest minimizer $y^*_n(i)$ of $G_n(i,\cdot)$ exists for every $i$, and $y^*_n(i)$ is nondecreasing in $i$.
--
--   Here "nonincreasing in $i$" means $i \preceq j \Rightarrow \Delta W_{n-1}(j,x) \le \Delta W_{n-1}(i,x)$, and similarly for the others. The finite-horizon optimal basestock levels thus inherit the order of the world states. Theorem 8 follows by letting $n \to \infty$.
--
--   **Formalization Note.** Part 3 asserts the existence of the smallest minimizers (proved in the paper as Theorem 1(a), printed "Theorem 4") and then the monotonicity of every function $i \mapsto y^*_n(i)$ of smallest minimizers.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 360, §4.2, Theorem 7 (proof in the Appendix, pp. 368–369)

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1
import Definitions.Def_SongZipkinFluct_Monotone_Recursion

namespace SongZipkinFluct.Monotone

/-- **Theorem 7** (Song and Zipkin 1993, §4.2, p. 360; proof in the Appendix, pp. 368–369). In the
linear-cost model (`K = 0`) with terminal cost `W₀ ≡ 0` (p. 357), for all `n ≥ 1` and fixed `x`:
(a) `ΔW_{n−1}(i, x)` is nonincreasing in `i`; (b) `ΔG_n(i, x)` is nonincreasing in `i`;
(c) `y*_n(i)`, the smallest minimizer of `G_n(i, ·)`, is nondecreasing in `i`.

**Formalization Note.** Part (c) is stated together with the existence of the smallest minimizers
`y*_n(i)` (Theorem 1(a) (printed "Theorem 4"), p. 357), and then for every function `ys` of
smallest minimizers. -/
theorem theorem7 {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ x : ℤ, Antitone (fun i => Δ (M.Wn 0 0 (n - 1)) i x)) ∧
      (∀ x : ℤ, Antitone (fun i => Δ (M.Gn 0 0 n) i x)) ∧
      (∃ ys : I → ℤ, ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys i)) ∧
      ∀ ys : I → ℤ, (∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys i)) → Monotone ys := by sorry

end SongZipkinFluct.Monotone
