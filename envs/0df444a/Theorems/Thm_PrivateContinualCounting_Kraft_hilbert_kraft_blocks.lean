-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_kraft_blocks
-- name    : PrivateContinualCounting.Kraft.hilbert_kraft_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:43:20.462451+00:00
-- url     : https://prove2.me/theorems/5e244d10-f717-486e-b69d-bb7b27ebeffd
-- title:
--   Hilbert blocks force the Kraft condition $\sum_k 1/g(2^k)<\infty$
-- statement:
--   This is the Hilbert-block argument of §3.2 in norm form. It uses only the monotonicity of the envelope and the envelope at the times $2^{2^i}$.
--
--   Let $(\alpha_j)_{j\ge0}$ and $(\beta_k)_{k\ge0}$ be nonnegative real sequences with $\sum_{k\ge0}\beta_k^2<\infty$ and $\sum_{j=0}^{m}\alpha_j\beta_{m-j}\ge1$ for every $m\ge0$. Let $g:[1,\infty)\to[1,\infty)$ be nondecreasing, and suppose that for some real constant $C$
--
--   $$\sum_{j<t}\alpha_j^2\ \le\ C\,(\ln t)^2\,g(\ln t)\qquad\text{for every integer }t\ge3.$$
--
--   Then the Kraft condition holds:
--
--   $$\sum_{k\ge0}\frac{1}{g(2^k)}<\infty .$$
--
--   With $\alpha_j=\|l_j\|$ and $\beta_k=\|r_k\|$ for LTI factors, this is the necessity half of Theorem 1.1(ii): a counter that cannot tell which doubly-dyadic time scale it is in must fund all of them from one finite budget, so their needs are summable.
--
--   **Formalization Note** $g$ is a real function on $\mathbb R$ whose hypotheses are imposed only on $[1,\infty)$; the conclusion is explicit summability.
-- source:
--   Kisung Park, Sharp Limits of Time Invariance in Private Continual Counting, STOC 2027 submission #86 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/86.pdf, p. 8 (PDF p. 10), §3.2 'Kraft necessity: Hilbert blocks', displayed estimate and the remark that the argument uses only monotonicity of g, the envelope at the times 2^(2^i), and is uniform in the coefficient dimension.

import Mathlib

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- §3.2 (Hilbert blocks) in norm form: an envelope bound on the prefix energies forces
the Kraft condition; only monotonicity of g is used. -/
theorem hilbert_kraft_blocks (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hconv : ∀ m : ℕ, 1 ≤ ∑ j ∈ Finset.range (m + 1), α j * β (m - j))
    (g : ℝ → ℝ) (hg1 : ∀ u : ℝ, 1 ≤ u → 1 ≤ g u) (hgm : MonotoneOn g (Set.Ici 1)) (C : ℝ)
    (hC : ∀ t : ℕ, 3 ≤ t →
      ∑ j ∈ Finset.range t, α j ^ 2 ≤ C * (Real.log (t : ℝ)) ^ 2 * g (Real.log (t : ℝ))) :
    Summable (fun k : ℕ => 1 / g ((2 : ℝ) ^ k)) := by sorry

end PrivateContinualCounting.Kraft
