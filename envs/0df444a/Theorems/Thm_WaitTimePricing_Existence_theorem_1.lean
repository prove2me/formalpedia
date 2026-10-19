-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_theorem_1
-- name    : WaitTimePricing.Existence.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:41.878976+00:00
-- url     : https://prove2.me/theorems/8e2b8870-7983-49da-9af6-e21a14e8d822
-- title:
--   Theorem 1 — $(\bar g,V^{\bar g})$ solves the DDEs (12)–(15), and $V^{\bar g}$ is decreasing and concave
-- statement:
--   Let $\bar g=\lim_{j\to\infty}g_{2^j}$ and $V^{\bar g}(w)=\lim_{j\to\infty}V^{\bar g}_{2^j}(w)$ be built from Algorithm 1 and the shooting values (23), for either objective of Lemma 1. Then:
--
--   1. the limit $\bar g=\lim_j g_{2^j}$ exists, and $V^{\bar g}_{2^j}(w)\to V^{\bar g}(w)$ for every $w\ge0$;
--   2. $g=\bar g$ and $V=V^{\bar g}$ solve the optimality equations (12)–(15):
--   $$\bar g=-V'(w)+\lambda\max\Big\{\max_{p\in[0,\Gamma(w)]}\big[\mathbf v(p)-\alpha c(w)+V(w+\mathtt t(p))-V(w)\big],0\Big\}\quad(0<w\le\bar w),$$
--   $$\bar g=\lambda\max\Big\{\max_{p\in[0,\Gamma(0)]}\big[\mathbf v(p)+V(\mathtt t(p))-V(0)\big],0\Big\},\qquad \bar g=-V'(w)\quad(w>\bar w),\qquad V(\bar w)=0;$$
--   3. the relative value function $V$ is nonincreasing and concave on $[0,\bar w+C]$.
--
--   This establishes existence of a solution of the delay differential optimality equations, which the paper then shows to be the optimal long-run average revenue or welfare rate.
--
--   **Formalization Note** The first item makes the statement about the paper's constructed $\bar g$ and $V^{\bar g}$ rather than default values of undefined limits. Convergence for $w\ge\bar w$ is immediate since $V^{\bar g}_{2^j}(w)=-(w-\bar w)\bar g$ there for every $j$ (the initialization (16), extended to $[\bar w,\infty)$). $V'(w)$ in (12) and (14) is asserted as an actual two-sided derivative. "Decreasing" means nonincreasing; monotonicity and concavity are asserted on $[0,\bar w+C]$, the domain of Proposition 6.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Theorem 1

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Theorem 1.

The value `g = ḡ` and the function `V = V^ḡ` solve the DDEs (12)–(15). Moreover, the relative
value function `V(w)` is decreasing and concave in `w`.

**Formalization Note.** `ḡ` (24) and `V^ḡ` (Proposition 6) are `limUnder` limits built from
Algorithm 1 (16)–(22) and (23); the first two conjuncts assert that these limits exist (for every
`w ≥ 0`; for `w ≥ w̄` the sequence is the constant `−(w − w̄)ḡ`, (16) extended to `[w̄, ∞)`), so the
theorem is about the paper's `ḡ`, `V^ḡ` and not about junk values. `SolvesDDE` encodes
(12)–(15) with `HasDerivAt` for `V′`. "Decreasing" is `AntitoneOn`; monotonicity and concavity
are asserted on `[0, w̄ + C]`, the domain of Proposition 6. -/
theorem theorem_1 (M : Model) (hM : M.Standing) (obj : Objective) :
    Tendsto (fun j : ℕ => gN M obj (2 ^ j)) atTop (nhds (gbar M obj)) ∧
    (∀ w : ℝ, 0 ≤ w →
      Tendsto (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) atTop (nhds (Vbar M obj w))) ∧
    SolvesDDE M obj (gbar M obj) (Vbar M obj) ∧
    AntitoneOn (Vbar M obj) (Icc 0 (wbar M + M.C)) ∧
    ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (Vbar M obj) := by sorry

end WaitTimePricing.Existence
