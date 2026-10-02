-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_gTilde_record_bound
-- name    : ShorNonsmooth.SpaceDilation.gTilde_record_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:07:00.321392+00:00
-- url     : https://prove2.me/theorems/f0da436f-0fa9-42e1-9b16-39c8145dbeed
-- title:
--   Theorem 3.2 — the record of $\|\tilde g_r\|$ is at most $d\sqrt{k(\alpha^2-1)}/\sqrt{\alpha^{2k/n}-1}$
-- statement:
--   Run the SDG method in $E_n$ ($n \ge 1$) with $B_0 = I$, an arbitrary stepsize rule and constant space-dilation coefficient $\alpha_k = \alpha > 1$, and suppose $\|g(x_k)\| \le d$ for all $k$, where $d > 0$. Write $\tilde g_r = B_r^* g(x_r)$. Then for every $k \ge 1$
--   $$
--   \min_{0 \le r \le k-1} \|\tilde g_r\| \;\le\; \frac{d\sqrt{k(\alpha^2 - 1)}}{\sqrt{\alpha^{2k/n} - 1}} .
--   $$
--
--   The right-hand side decreases like $\sqrt{k}\,\alpha^{-k/n}$, so the best transformed gradient among the first $k$ iterations decays geometrically, with an explicit constant. Theorem 3.4 converts this into a bound on the record function value.
--
--   **Formalization Note** The book writes the minimum as $v_k = \min_{1 \le r \le k} \|\tilde g_r\|$. Its proof (pp. 55–56) derives a contradiction from lower bounds on $\|\tilde g_r\|$ that control the growth of the largest eigenvalue of $A_{r+1}$ from $A_r$, starting at $A_0 = I$ with $\lambda^{(0)} = 1$, and so uses exactly $\tilde g_0, \dots, \tilde g_{k-1}$; the Lean statement is the bound the proof establishes, with the minimum over $0 \le r \le k-1$. The proof takes $A_0 = I$, and the bound is not invariant under rescaling $B_0$, so $B_0 = I$ is assumed. The minimum is written as the existence of an index $r < k$ attaining the bound.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 55, Theorem 3.2 (with $v_k$ defined on p. 55), proof pp. 55–56

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), p. 55, Theorem 3.2, in the form its proof (pp. 55–56) establishes. Run the SDG
method with `B₀ = I` (the proof's `A₀ = I`), any stepsize rule `h`, constant coefficients
`α_k = α > 1`, and a selection `g` with `‖g(x_k)‖ ≤ d` for all `k`. Then for every `k ≥ 1`,
`min_{0 ≤ r ≤ k-1} ‖g̃_r‖ ≤ d √(k(α² - 1)) / √(α^{2k/n} - 1)`.
(The book writes the minimum over `1 ≤ r ≤ k`; its proof bounds `g̃_0, …, g̃_{k-1}`, which drive
`A_1, …, A_k`, starting from `λ^{(0)} = 1`. See the mission's HARD.md.) -/
theorem gTilde_record_bound {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (d α : ℝ) (hd : 0 < d) (hα : 1 < α)
    (hg : ∀ k : ℕ,
      ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) k).x‖ ≤ d)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ r : ℕ, r < k ∧
      ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) r‖ ≤
        d * Real.sqrt (k * (α ^ 2 - 1)) / Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1) := by sorry

end ShorNonsmooth.SpaceDilation
