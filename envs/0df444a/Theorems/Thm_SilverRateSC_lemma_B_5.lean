-- Prove2me | Theorems.Thm_SilverRateSC_lemma_B_5
-- name    : SilverRateSC.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:45:45.485056+00:00
-- url     : https://prove2.me/theorems/dd2571a1-dce7-4136-bd77-7bdfa36e2012
-- title:
--   Lemma B.5 — $[U_\Lambda(g)/c]^{1/p}\le\Lambda^{1/p}+\sum_j(a+g_j)^{1/p}$
-- statement:
--   Fix $1\le c\le2$, $a\ge8$, $p=p(c)$. For every $g\in[0,\infty)^r$ and $\Lambda\ge a$,
--   $$\Bigl[\frac{U_\Lambda(g)}c\Bigr]^{1/p}\le\Lambda^{1/p}+\sum_{j=1}^r(a+g_j)^{1/p},\qquad U_\Lambda(g):=\sup_{B\in[0,\infty)^r}V_\Lambda(g,B),$$
--   where $V_\Lambda(g,B)$ is the minimum checkpoint cost of Appendix B.
--
--   The bound turns the combinatorial checkpoint problem into the power-$p$ growth $a\,m^p$ that appears in Lemma 4.1.
--
--   Differences from the source:
--   - encoding: [U_Λ(g)/c]^{1/p} ≤ RHS with U_Λ(g) = sup_{B ∈ [0,∞)^r} V_Λ(g,B) → ∀ B ∈ [0,∞)^r, [V_Λ(g,B)/c]^{1/p} ≤ RHS; reason: t ↦ (t/c)^{1/p} is nondecreasing and continuous on [0,∞), so the two forms are equivalent (and the supremum is finite)
--   - encoding: standing assumptions of Appendix B: 1 ≤ c ≤ 2, a ≥ 8, p = p(c); vectors in [0,∞)^r → explicit hypotheses; vectors as ℕ → ℝ read at positions 1, …, r; reason: same data
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma B.5, p.41; definitions §B.1, pp.37–38

import Mathlib
import Definitions.Def_SilverRateSC_pOf
import Definitions.Def_SilverRateSC_costV

namespace SilverRateSC

/-- **Lemma B.5.** Fix `1 ≤ c ≤ 2`, `a ≥ 8`, `p = p(c)`. For every `g ∈ [0, ∞)^r` and `Λ ≥ a`,
`[U_Λ(g)/c]^{1/p} ≤ Λ^{1/p} + ∑_{j=1}^r (a + g_j)^{1/p}`, where
`U_Λ(g) := sup_{B ∈ [0,∞)^r} V_Λ(g, B)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma B.5, p. 41 (definitions §B.1, pp. 37–38).

**Formalization Note** The supremum over `B` is unfolded: the bound is stated for every
`B ∈ [0, ∞)^r`, which is equivalent since `t ↦ (t/c)^{1/p}` is nondecreasing and continuous on
`[0, ∞)` (and forces the supremum to be finite). Vectors are `ℕ → ℝ` at positions `1, …, r`;
`V_Λ` is `costV`. -/
theorem lemma_B_5 (a c Λ : ℝ) (r : ℕ) (g : ℕ → ℝ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (ha : 8 ≤ a)
    (hΛ : a ≤ Λ) (hg : ∀ j ∈ Finset.Icc 1 r, 0 ≤ g j) :
    ∀ B : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 r, 0 ≤ B j) →
      (costV a c Λ r g B / c) ^ (1 / pOf c) ≤
        Λ ^ (1 / pOf c) + ∑ j ∈ Finset.Icc 1 r, (a + g j) ^ (1 / pOf c) := by sorry

end SilverRateSC
