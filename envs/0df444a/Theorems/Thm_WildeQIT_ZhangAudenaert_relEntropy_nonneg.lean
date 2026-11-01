-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_relEntropy_nonneg
-- name    : WildeQIT.ZhangAudenaert.relEntropy_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:18.183971+00:00
-- url     : https://prove2.me/theorems/5c9afab7-7ca5-4951-b286-7225053c224f
-- title:
--   Theorem 10.7.1 (Non-Negativity of Relative Entropy): $D(p\|q)\ge0$ for subnormalized $q$, with equality iff $p=q$
-- statement:
--   Let $p$ be a probability distribution on a finite alphabet $\mathcal X$, and let $q:\mathcal X\to[0,1]$ be a function with $\sum_x q(x)\le 1$ (not necessarily a probability distribution). Let
--
--   $$
--   D(p\|q)=\begin{cases}\sum_x p(x)\log\dfrac{p(x)}{q(x)} & \text{if } \operatorname{supp}(p)\subseteq\operatorname{supp}(q),\\[2pt] +\infty & \text{otherwise}\end{cases}
--   $$
--
--   be the relative entropy (Definition 10.5.2, in bits). Then
--
--   $$
--   D(p\|q)\ge 0,
--   $$
--
--   and $D(p\|q)=0$ if and only if $p=q$ (as functions on $\mathcal X$).
--
--   This is the inequality from which the maximal value of entropy, Theorem 10.2.1, Theorem 10.4.1 and strong subadditivity follow; allowing subnormalized $q$ is what the proof of the data-processing inequality (Theorem 10.7.2) needs.
--
--   **Formalization Note** $D(p\|q)$ is the published extended-real relative entropy (`WildeQIT.relEntropy`), so the value $+\infty$ is represented exactly.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.7.1, eq. (10.44), p. 299

import Mathlib
import Definitions.Def_WildeQIT_relEntropy

namespace WildeQIT.ZhangAudenaert

/-- **Theorem 10.7.1 (Non-Negativity of Relative Entropy).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.7.1, (10.44),
p. 299: "Let `p(x)` be a probability distribution over the alphabet `𝒳` and let `q : 𝒳 → [0, 1]`
be a function such that `∑_x q(x) ≤ 1`. Then the relative entropy `D(p‖q)` is non-negative:
`D(p‖q) ≥ 0`, and `D(p‖q) = 0` if and only if `p = q`."

**Formalization Note.** `q` is a real function on the finite alphabet `α` with values in
`[0, 1]` (it need not sum to one); `D(p‖q) = relEntropy p q` is the published extended-real
relative entropy in bits, `+∞` when `supp p ⊄ supp q` (Definition 10.5.2). "`p = q`" is
equality of the functions `p.prob` and `q`. -/
theorem relEntropy_nonneg {α : Type} [Fintype α] (p : FinDist α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hsum : ∑ x, q x ≤ 1) :
    0 ≤ relEntropy p q ∧ (relEntropy p q = 0 ↔ p.prob = q) := by sorry

end WildeQIT.ZhangAudenaert
