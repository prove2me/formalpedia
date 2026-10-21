-- Prove2me | Theorems.Thm_SeqMechExPost_Optimal_lemma_6
-- name    : SeqMechExPost.Optimal.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:15.209027+00:00
-- url     : https://prove2.me/theorems/9b2bc0ed-5ba9-4549-a9f7-1dbd10d8a4de
-- title:
--   Lemma 6, p. 12 — running the single-day optimizers (X^{c_{i−1}}_i, P^{c_{i−1}}_i) forward from c_0 = argmax ĝ_1 solves the adjusted problem
-- statement:
--   Let $\hat g_1,\dots,\hat g_k$ be the cumulative tradeoff functions of Definition 2. Suppose that for every day $i$ and every $c \ge 0$, $(X^c_i, P^c_i)$ is an optimizer of day $i$'s tight tradeoff problem with bound $c$, and that $(c,v) \mapsto X^c_i(v)$ and $(c,v) \mapsto P^c_i(v)$ are measurable. Let $c_0 \ge 0$ maximize $\hat g_1(c)$ over $c \ge 0$. Define the adjusted mechanism $(x,\hat p)$ recursively: $(x_1,\hat p_1) = (X^{c_0}_1, P^{c_0}_1)$ and, for $i \ge 2$,
--   $$x_i(v_{\le i}) = X^{c_{i-1}}_i(v_i), \qquad \hat p_i(v_{\le i}) = P^{c_{i-1}}_i(v_i), \qquad c_{i-1} = v_{i-1}x_{i-1}(v_{<i}) - \hat p_{i-1}(v_{<i}).$$
--   Then $(x,\hat p)$ is an optimal solution of the adjusted problem (11)–(13): it is feasible and its objective is at least that of every feasible adjusted mechanism.
--
--   This is the characterization of the optimal adjusted mechanism, from which Theorem 7 follows through Lemma 3.
--
--   **Formalization Note** Days are 0-based (Lean day $i$ is paper day $i+1$; `cState X P c0 n` is $c_n$). The optimizers, their joint measurability and the maximizer $c_0$ are hypotheses: Definition 2 and the lemma presuppose them ("given solutions"). The optimizers are required only at $c \ge 0$ and $c_0$ maximizes over $c \ge 0$, because in the paper $\hat g_i(c) = -\infty$ for $c < 0$ while the Lean value there is the junk $0$.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 12 (PDF 13), Lemma 6

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff

namespace SeqMechExPost.Optimal

theorem lemma_6 {k : ℕ} (I : Instance k) (hk : 0 < k)
    (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) (hc0 : 0 ≤ c0 ∧ ∀ c, 0 ≤ c → gHat I ⟨0, hk⟩ c ≤ gHat I ⟨0, hk⟩ c0) :
    (thm7Adj X P c0).AdjOptimal I := by sorry

end SeqMechExPost.Optimal
