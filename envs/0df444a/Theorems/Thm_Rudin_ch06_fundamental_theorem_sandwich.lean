-- Prove2me | Theorems.Thm_Rudin_ch06_fundamental_theorem_sandwich
-- name    : Rudin.ch06_fundamental_theorem_sandwich
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T20:49:07.3788+00:00
-- url     : https://prove2.me/theorems/6d3eed34-7f20-4035-860b-9fcb9b74a749
-- title:
--   Theorem 6.21, sandwich form — $F(b)-F(a)$ between the lower and upper integrals of $F'$
-- statement:
--   Let $a \le b$, let $f, F : \mathbb{R} \to \mathbb{R}$, and suppose $F$ is differentiable at every point of $[a,b]$ with $F'(x) = f(x)$ there. No integrability of $f$ is assumed, and boundedness is assumed only on one side at a time. Then, with $\underline{\int}$ and $\overline{\int}$ the lower and upper Riemann integrals of Rudin's Definition 6.2 (the case $\alpha(x) = x$):
--
--   1. if $f$ is bounded below on $[a,b]$, then
--   $$\underline{\int_a^b} f(x)\,dx \;\le\; F(b) - F(a);$$
--
--   2. if $f$ is bounded above on $[a,b]$, then
--   $$F(b) - F(a) \;\le\; \overline{\int_a^b} f(x)\,dx;$$
--
--   3. consequently, if $f$ is bounded below and $f \in \mathcal{R}$ on $[a,b]$, then
--   $$\int_a^b f(x)\,dx \;\le\; F(b) - F(a).$$
--
--   The mechanism is the mean value theorem applied on each subinterval of a partition $a = x_0 \le x_1 \le \dots \le x_n = b$: there is $t_i \in [x_{i-1}, x_i]$ with $F(x_i) - F(x_{i-1}) = f(t_i)\,\Delta x_i$. If $f$ is bounded below, the infimum $m_i$ of $f$ on the subinterval is a genuine infimum and $m_i \le f(t_i)$, so summing and telescoping gives $L(P,f) \le F(b) - F(a)$ for every partition $P$; taking the supremum over $P$ gives (1). Symmetrically, boundedness above gives $F(b) - F(a) \le U(P,f)$ and hence (2).
--
--   Taken together, (1) and (2) contain Rudin's Theorem 6.21 for bounded $f$: if $f$ is bounded and integrable, the upper and lower integrals agree and are therefore both equal to $F(b) - F(a)$. Each one-sided hypothesis is needed for its own half: in this formalization suprema and infima of unbounded sets take a default value, and an increasing everywhere differentiable $F$ with unbounded derivative shows that (2) fails without boundedness above, its reflection $-F$ that (1) fails without boundedness below.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6: Theorem 6.21 (p. 134), sharpened form of the estimate in its proof (each partition sum is compared with F(b)-F(a) via the mean value theorem, Theorem 5.10, p. 108).

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.21 in sandwich form, with one-sided boundedness and no integrability
hypothesis.  If `F` is differentiable on `[a, b]` with `F' = f`, then the mean value theorem
squeezes `F b - F a` between the lower and upper Darboux sums of `f`: as soon as `f` is bounded
below on `[a, b]`, the lower integral of `f` is at most `F b - F a`, and as soon as `f` is
bounded above, `F b - F a` is at most the upper integral of `f`.  In particular, for `f` bounded
below and `f ∈ ℛ` on `[a, b]`, `∫ₐᵇ f dx ≤ F b - F a`. -/
theorem ch06_fundamental_theorem_sandwich (a b : ℝ) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    ((∃ m, ∀ x ∈ Set.Icc a b, m ≤ f x) → lowerIntegral a b f id ≤ F b - F a) ∧
      ((∃ M, ∀ x ∈ Set.Icc a b, f x ≤ M) → F b - F a ≤ upperIntegral a b f id) ∧
      ((∃ m, ∀ x ∈ Set.Icc a b, m ≤ f x) → RiemannIntegrable a b f →
        RiemannIntegral a b f ≤ F b - F a) := by sorry

end Rudin
