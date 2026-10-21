-- Prove2me | Theorems.Thm_SeqMechExPost_Optimal_theorem_7
-- name    : SeqMechExPost.Optimal.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:19.998831+00:00
-- url     : https://prove2.me/theorems/34434f9f-1a95-4384-854d-d311a7909ed5
-- title:
--   Theorem 7, p. 12 — the backward-induction mechanism built from the cumulative tradeoff functions ĝ_i is revenue-optimal among PIC, ex-post IR mechanisms
-- statement:
--   A seller sells $k \ge 1$ items to one buyer over $k$ days; the buyer's value $v_i$ for item $i$ lies in $[\underline v_i, \bar v_i] \subseteq [0,\infty)$, is drawn from a probability law $\mu_i$, is independent across days, and is learned at the start of day $i$.
--
--   Let $\hat g_1,\dots,\hat g_k$ be the cumulative tradeoff functions of Definition 2, and suppose that for every day $i$ and every $c \ge 0$, $(X^c_i, P^c_i)$ is an optimizer of day $i$'s tight surplus-utility-tradeoff problem with bound $c$, with $(c,v)\mapsto X^c_i(v)$ and $(c,v)\mapsto P^c_i(v)$ measurable. Let $c_0 \ge 0$ maximize $\hat g_1(c)$ over $c \ge 0$. Consider the mechanism that on each day $i \ge 1$, when the buyer reports $v_i$,
--
--   1. allocates the item with probability $X^{c_{i-1}}_i(v_i)$;
--   2. charges $v_i X^{c_{i-1}}_i(v_i)$ if $i < k$ and $P^{c_{i-1}}_i(v_i)$ if $i = k$;
--   3. updates the state to $c_i = v_i X^{c_{i-1}}_i(v_i) - P^{c_{i-1}}_i(v_i)$.
--
--   Then this mechanism is an optimal mechanism for the original problem: it is periodic incentive compatible (1) and ex-post individually rational (2), and its expected revenue
--   $$\mathbf E_{v_1,\dots,v_k}\Big[\sum_{i=1}^k p_i(v_{\le i})\Big]$$
--   is at least that of every periodic incentive compatible, ex-post individually rational mechanism.
--
--   The theorem reduces the $k$-day revenue maximization problem under ex-post participation constraints to $k$ one-dimensional problems solved by backward induction, with a single scalar state, the buyer's realized adjusted utility, carried forward.
--
--   **Formalization Note** Days are 0-based: Lean day $i$ is the paper's day $i+1$, `gHat I ⟨0, hk⟩` is $\hat g_1$, and `cState X P c0 n` is $c_n$. Step 0 of the theorem ("define … $(X^c_i, P^c_i)$ … as solutions"; "set $c_0$ equal to the maximizer") presupposes the optimizers and the maximizer, so they are hypotheses; the maximization is over $c \ge 0$, where the paper's $\hat g_1$ is finite. Added and disclosed: joint measurability of the optimizers in $(c,v)$, without which the day-$i$ rule $v \mapsto X^{c_{i-1}(v)}_i(v_i)$ need not be measurable and the expectations in (1) and (3) would not be defined; general probability laws on the type intervals in place of densities (the paper says its results also apply to discrete support); and measurability and integrability of competing mechanisms (admissibility). The competitor class is every feasible mechanism of the original problem, not only those of the theorem's form.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 12 (PDF 13), Theorem 7

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff

namespace SeqMechExPost.Optimal

theorem theorem_7 {k : ℕ} (I : Instance k) (hk : 0 < k)
    (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) (hc0 : 0 ≤ c0 ∧ ∀ c, 0 ≤ c → gHat I ⟨0, hk⟩ c ≤ gHat I ⟨0, hk⟩ c0) :
    (thm7Mech X P c0).IsOptimal I := by sorry

end SeqMechExPost.Optimal
