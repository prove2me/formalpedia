-- Prove2me | Theorems.Thm_RestartPD_Fixed_theorem_1
-- name    : RestartPD.Fixed.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:42.387994+00:00
-- url     : https://prove2.me/theorems/4884d106-6fbd-4b4a-b8a8-7b105b95b3bb
-- title:
--   Theorem 1, p. 17 — with fixed-frequency restarts on an α-sharp problem, dist(z^{n,0}, Z⋆) ≤ βⁿ dist(z^{0,0}, Z⋆)
-- statement:
--   Assume the standing assumptions of (1): $X$, $Y$ closed and convex, $L$ differentiable, convex in $x$ and concave in $y$, and $Z^\star \neq \emptyset$. Let $\|\cdot\|$ be a semi-norm, and let the base primal-dual algorithm satisfy Property 3 with constants $q, C > 0$. Let $\alpha > 0$ and $\beta \in (0, 1)$, and run Algorithm 1 from $z^{0,0} \in Z$ with the fixed-frequency restart rule (29): restart every
--   $$t^\star = \left\lceil \frac{2C(q+2)}{\alpha\beta} \right\rceil$$
--   inner steps, $z^{n+1,0} = \bar z^{n,t^\star}$. Suppose (1) is $\alpha$-sharp on $W_R(z^{0,0})$ with
--   $$R = \frac{q+2}{1-\beta} \operatorname{dist}(z^{0,0}, Z^\star).$$
--   Then for every outer iteration $n \ge 0$,
--   $$\operatorname{dist}(z^{n,0}, Z^\star) \le \beta^n \operatorname{dist}(z^{0,0}, Z^\star). \tag{31}$$
--
--   With PDHG, EGM, PPM or ADMM as the base algorithm and the LP sharpness of Lemma 5, this gives linear convergence of restarted primal-dual methods for linear programming.
--
--   **Formalization Note** The base algorithm is the set of its admissible output sequences from each start; Property 3 holds for every start in $Z$ and every run. The restart length is the natural number $\lceil 2C(q+2)/(\alpha\beta) \rceil$ (`Nat.ceil`). $\alpha > 0$ is assumed (a sharpness constant is positive, and $t^\star$ divides by $\alpha$). $Z^\star \neq \emptyset$ replaces the page's "non-empty feasible region and bounded optimal value". Sharpness is assumed only on $W_R(z^{0,0})$ and only for radii in $(0, \operatorname{diam}(W_R(z^{0,0}))]$, as in Definition 1.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 17, Theorem 1 (31)

import Mathlib
import Definitions.Def_RestartPD_Fixed_Algorithms

namespace RestartPD.Fixed

/-- Theorem 1 (Fixed frequency restarts), p. 17: if the base algorithm satisfies Property 3 with
`q, C`, the problem is `α`-sharp on `W_R(z^{0,0})` with `R = ((q + 2)/(1 − β)) dist(z^{0,0}, Z⋆)`,
and Algorithm 1 restarts every `t⋆ = ⌈2C(q + 2)/(αβ)⌉` inner steps (29), then
`dist(z^{n,0}, Z⋆) ≤ βⁿ dist(z^{0,0}, Z⋆)` for every `n ≥ 0` (31). -/
theorem theorem_1 {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs (Nat.ceil (2 * C * (q + 2) / (α * β))) z zb)
    (hsharp : IsSharpOn L X Y p α
      (Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0))) :
    ∀ k : ℕ, distZ L X Y p (z k) ≤ β ^ k * distZ L X Y p (z 0) := by sorry

end RestartPD.Fixed
