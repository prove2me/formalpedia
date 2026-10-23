-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_proposition_1_ineq5
-- name    : UniversalBarrier.NSC.proposition_1_ineq5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:43.524423+00:00
-- url     : https://prove2.me/theorems/fa800381-361f-4680-be73-c41dcfc9cc02
-- title:
--   Proposition 1, inequality (5), p. 4 — μ₁²(p) ≤ k(k+2)μ₂²(p) for 1/(k−1)-concave p with 0 ∈ Supp(p)
-- statement:
--   Let $k\ge1$ be an integer and let $p$ be a probability density on $\mathbb R$ that is $\tfrac1{k-1}$-concave (for $k=1$: $\infty$-concave). Suppose $0\in\operatorname{Supp}(p)=\operatorname{cl}\{t:\ p(t)>0\}$. Then
--   $$\mu_1^2(p)\ \le\ k(k+2)\,\mu_2^2(p),$$
--   where $\mu_1(p)$ is the mean and $\mu_2^2(p)$ the variance of $p$.
--
--   This is the second half of Proposition 1. Applied with $k=n$ to the marginal of $K^\circ(x)$, it gives the $n$-bound (2) in Theorem 2. The inequality is sharp, with equality for $k\,t^{k-1}\mathbb 1_{[0,1]}(t)$.
--
--   **Formalization Note.** $s$-concavity is quantified over support points (the literal Definition 5 admits no density); $\tfrac1{k-1}$-concave is encoded with index $m=k-1$, and $m=0$ is the $\max$ clause ($s=+\infty$). A density is a non-negative function with integral $1$; this forces integrability, and a $\tfrac1{k-1}$-concave density has bounded support, so all moments are genuine integrals.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 4, Proposition 1, inequality (5)

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

open MeasureTheory

namespace UniversalBarrier.NSC

theorem proposition_1_ineq5 (k : ℕ) (hk : 1 ≤ k) (p : ℝ → ℝ) (hp0 : ∀ t, 0 ≤ p t)
    (hp1 : ∫ t, p t = 1) (hpc : IsOneOverMConcave (k - 1) p)
    (h0 : (0 : ℝ) ∈ closure {t : ℝ | 0 < p t}) :
    mu1 p ^ 2 ≤ (k : ℝ) * ((k : ℝ) + 2) * mu2sq p := by sorry

end UniversalBarrier.NSC
