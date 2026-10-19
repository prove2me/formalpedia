-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_lemma_7_1
-- name    : PrivSeqLearn.QueryComplexity.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:22.237691+00:00
-- url     : https://prove2.me/theorems/9fadbda7-fa1b-45a9-8c8f-5809db29a6b5
-- title:
--   Lemma 7.1, p. 20 — for an accurate strategy and every seed, some x ∈ (0, δ) has at least log(δ/ϵ) of its queries in (0, δ)
-- statement:
--   Let $\epsilon > 0$ and $0 < \delta \le 1$, and fix a learner strategy $\phi$ of length $N$ that satisfies the accuracy constraint. For every seed $y$ there exists $x \in (0, \delta)$ such that
--   $$\#\{k \in \{1, \dots, N\} : q_k(x,y) \in (0,\delta)\} \ge \left\lceil \log_2 \frac{\delta}{\epsilon} \right\rceil.$$
--
--   The paper calls this essentially the classical optimality of bisection on an interval (Waeber et al., 2013) and omits its proof; it supplies the $\log(\delta/\epsilon)$ term of the lower bound.
--
--   **Formalization Note** Queries are counted by index, so repeated values count with multiplicity. The hypothesis $\delta \le 1$ is added: the lemma needs $(0,\delta) \subseteq [0,1)$, the range of admissible true values, and the paper applies it with $\delta \le 1/L$. Membership in $\Phi_N$ is not assumed. The logarithm is base 2 and rounded up (footnote 1, p. 4).
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 20, Lemma 7.1

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

namespace PrivSeqLearn.QueryComplexity

/-- Lemma 7.1 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 20): fix a learner strategy `φ` that satisfies the accuracy constraint.
For every seed `y` there is `x ∈ (0, δ)` such that at least `⌈log₂(δ/ϵ)⌉` of the queries in `q(x, y)`
belong to `(0, δ)`.

**Formalization Note** Queries are counted by index `k`. The hypotheses `ϵ > 0`, `δ > 0` are the
paper's standing assumptions; `δ ≤ 1` is added so that `(0, δ) ⊆ [0, 1)` consists of admissible true
values (the paper applies the lemma with `δ ≤ 1/L`). Membership in `Φ_N` is not assumed. -/
theorem lemma_7_1 {N : ℕ} (ϵ δ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ) (hϵ : 0 < ϵ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (y : Fin φ.Ybar) :
    ∃ x ∈ Set.Ioo (0 : ℝ) δ,
      ⌈Real.logb 2 (δ / ϵ)⌉₊ ≤ {k : Fin N | queries φ x y k ∈ Set.Ioo (0 : ℝ) δ}.ncard := by sorry

end PrivSeqLearn.QueryComplexity
