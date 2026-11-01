-- Prove2me | Theorems.Thm_SmallLossGraph_lemma_3_1
-- name    : SmallLossGraph.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:52.029293+00:00
-- url     : https://prove2.me/theorems/57ecdeb6-cacb-414d-8578-a4fd7cbf9691
-- title:
--   Lemma 3.1 — the frozen mass is at most $\varepsilon'$, so $w_i\le p_i/(1-\varepsilon')$
-- statement:
--   Let $G$ be a graph on the arms whose independent sets have at most $\alpha$ vertices, $p$ a probability vector on the arms and $\varepsilon'>0$. Let $F$ be the frozen set of one round of Algorithm 1 with thresholds $\gamma=\varepsilon'/(4\alpha)$, $\gamma'=\gamma/3$, and $w$ its sampling distribution. Then
--
--   1. the frozen mass is small:
--   $$
--   \sum_{i\in F}p_i\le\varepsilon' ;
--   $$
--   2. if $\varepsilon'<1$, every non-frozen arm $i\notin F$ satisfies
--   $$
--   w_i\le\frac{p_i}{1-\varepsilon'} .
--   $$
--
--   The second clause is what lets the algorithm's loss be compared to the loss of the full-information algorithm up to the factor $1/(1-\varepsilon')$.
--
--   Differences from the source:
--   - reading: any non-frozen arm increases its probability due to freezing by a factor of at most (1 − ε′) → w_i ≤ p_i/(1 − ε′) for every i ∉ F; reason: the normalization of line 5 multiplies p_i by 1/(1 − Σ_F p) ≤ 1/(1 − ε′); the printed (1 − ε′) names the divisor
--   - encoding: the second clause, stated without a range for ε′ → the second clause under ε′ < 1; reason: for ε′ ≥ 1 the factor 1/(1 − ε′) is undefined or negative; the guard only excludes that case
--   - encoding: α an upper bound on the size of maximum independent sets (Algorithm 1) → IndepBound G α: every independent set of G has at most α vertices; reason: the same condition α(G) ≤ α, stated without Mathlib's indepNum supremum
--   - encoding: round t of Algorithm 1 (p^t, G^t, ℓ^t) → one round with the superscript t dropped; reason: the statement concerns a single round
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, Lemma 3.1, p.9

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Lemma 3.1 (total frozen mass).**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, Lemma 3.1, p.9: "At every round `t`, the total
probability of frozen arms is at most `ε′`: `∑_{i∈F^t} p^t_i ≤ ε′`, and hence any non-frozen arm
`i` increases its probability due to freezing by a factor of at most `(1 − ε′)`."

Let `α` bound the independent sets of `G`, let `p` be a probability vector, `ε′ > 0`, and let
`F` be the frozen set of Algorithm 1 with `γ = ε′/(4α)`, `γ′ = γ/3`. Then
1. `∑_{i∈F} p_i ≤ ε′`;
2. if `ε′ < 1`, every non-frozen arm `i` has `w_i ≤ p_i / (1 − ε′)`.

**Formalization Note** One round. "Increases its probability by a factor of at most `(1 − ε′)`"
is read as `w_i ≤ p_i/(1 − ε′)` (the normalization of line 5 divides by `1 − ∑_F p ≥ 1 − ε′`);
`ε′ < 1` excludes the case where that factor is undefined. -/
theorem lemma_3_1 {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ) (hα : IndepBound G α)
    (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ε' : ℝ) (hε' : 0 < ε') :
    ∑ i ∈ frozen G p (gamma ε' α) (gammaPrime ε' α), p i ≤ ε' ∧
      (ε' < 1 → ∀ i, i ∉ frozen G p (gamma ε' α) (gammaPrime ε' α) →
        sampling G p (gamma ε' α) (gammaPrime ε' α) i ≤ p i / (1 - ε')) := by sorry

end SmallLossGraph
