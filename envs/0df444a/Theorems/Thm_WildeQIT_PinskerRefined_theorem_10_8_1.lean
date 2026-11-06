-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_theorem_10_8_1
-- name    : WildeQIT.PinskerRefined.theorem_10_8_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:06.856643+00:00
-- url     : https://prove2.me/theorems/39a350f3-2a8a-4bc0-beb7-cb792def4aa4
-- title:
--   Theorem 10.8.1 (Pinsker Inequality) — $D(p\|q)\ge\frac{1}{2\ln 2}\|p-q\|_1^2$
-- statement:
--   Let $p$ be a probability distribution on a finite alphabet $\mathcal X$ and let $q:\mathcal X\to[0,1]$ satisfy $\sum_x q(x)\le 1$. Then
--
--   $$
--   D(p\|q)\ge\frac{1}{2\ln 2}\,\|p-q\|_1^2, \tag{10.127}
--   $$
--
--   where $D$ is the relative entropy in bits (Definition 10.5.2) and $\|p-q\|_1=\sum_x|p(x)-q(x)|$ (Definition 10.7.1).
--
--   Pinsker's inequality turns a small relative entropy into a small trace distance. It strengthens the non-negativity of relative entropy, and it is the tool behind the lower bounds of Theorems 10.8.2 and 10.8.3.
--
--   **Formalization Note** $D$ is `relEntropy` with values in the extended reals ($+\infty$ off support). The bound $q(x)\le 1$ is not a separate hypothesis because it follows from $q\ge 0$ and $\sum_x q(x)\le 1$.
--
--   Differences from the source:
--
--   - encoding: q : X → [0, 1] with Σ_x q(x) ≤ 1 → q ≥ 0 and Σ_x q(x) ≤ 1; reason: q(x) ≤ 1 follows from these two hypotheses, so the set of admissible q is the same
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.8.1, p. 311, Eq. (10.127)

import Definitions.Def_WildeQIT_relEntropy
import Definitions.Def_WildeQIT_classicalTraceDist

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Theorem 10.8.1 (Pinsker Inequality)**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 311: let `p` be a probability distribution
on a finite alphabet `𝒳` and `q : 𝒳 → [0, 1]` with `∑_x q(x) ≤ 1`. Then
`D(p‖q) ≥ (1 / (2 ln 2)) ‖p − q‖₁²` (10.127).

**Formalization Note** `D` is the published `relEntropy` (bits, `EReal`, `+∞` off support,
Definition 10.5.2) and `‖p − q‖₁ = ∑_x |p(x) − q(x)|` is the published `classicalTraceDist`
(Definition 10.7.1). The book's `q(x) ≤ 1` is not a separate hypothesis: it follows from
`q ≥ 0` and `∑_x q(x) ≤ 1`. -/
theorem theorem_10_8_1 {α : Type} [Fintype α] (p : FinDist α) (q : α → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x ≤ 1) :
    ((1 / (2 * Real.log 2) * classicalTraceDist p.prob q ^ 2 : ℝ) : EReal) ≤
      relEntropy p q := by sorry

end WildeQIT.PinskerRefined
