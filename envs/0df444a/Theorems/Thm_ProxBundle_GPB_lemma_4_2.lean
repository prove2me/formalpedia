-- Prove2me | Theorems.Thm_ProxBundle_GPB_lemma_4_2
-- name    : ProxBundle.GPB.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:19.980982+00:00
-- url     : https://prove2.me/theorems/0266c507-f719-47d1-b781-636c3c6b0b8e
-- title:
--   Lemma 4.2, pp. 13–14 — serious-step recursion
-- statement:
--   Consider the abstract serious-iterate sequences of Lemma 4.1 for a hybrid convex composite problem, with proximal parameter $\lambda>0$, tolerance $\bar\varepsilon>0$, and $\lambda_\mu=\lambda/(1+\lambda\mu)$. For $u\in D$ and every $k\ge1$,
--   $$
--   \phi(\hat y_k)-\phi(u)\le\frac{\|\hat x_{k-1}-u\|^2}{2\lambda}-\frac{\|\hat x_k-u\|^2}{2\lambda_\mu}+\frac{\bar\varepsilon}{2}.
--   $$
--   If $K\ge1$ is at least the serious-iteration threshold of Corollary B.2, one of the first $K$ auxiliary serious iterates is a $\bar\varepsilon$-solution relative to $u$. If $u$ is optimal, then $\|\hat x_k-u\|^2\le\|x_0-u\|^2+\lambda k\bar\varepsilon$.
--
--   This is the analytic recursion underlying the count of serious iterations.
--
--   **Formalization Note** Part (c) requires optimal $u$: the printed unrestricted claim is false. The $\mu=0$ case uses the convention of Corollary B.2. The abstract sequence model explicitly keeps $\hat y_k\in D$.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, pp. 13–14, Lemma 4.2, (44)–(45)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Lemma 4.2, pp. 13–14. Part (c) requires `u` to be optimal; the printed
statement omits this condition although its proof uses it. -/
theorem lemma_4_2 {n : ℕ} (P : Instance n) (μ lam ε : ℝ)
    (x0 u : E n) (xh yh : ℕ → E n) (Γh : ℕ → E n → ℝ)
    (hμ : 0 ≤ μ) (hA1 : P.A1 μ) (hlam : 0 < lam) (hε : 0 < ε)
    (hhat : IsHat P μ lam ε x0 xh yh Γh) (hu : u ∈ P.D) :
    (∀ k : ℕ, 1 ≤ k →
      P.φ (yh k) - P.φ u ≤
        ‖xh (k - 1) - u‖ ^ 2 / (2 * lam) -
        ‖xh k - u‖ ^ 2 / (2 * lamMu μ lam) + ε / 2) ∧
    (∀ K : ℕ, 1 ≤ K → serBound μ lam ε (‖x0 - u‖ ^ 2) ≤ (K : ℝ) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ P.φ (yh k) - P.φ u ≤ ε) ∧
    (P.IsOpt u → ∀ k : ℕ, 1 ≤ k →
      ‖xh k - u‖ ^ 2 ≤ ‖x0 - u‖ ^ 2 + lam * (k : ℝ) * ε) := by sorry

end ProxBundle.GPB
