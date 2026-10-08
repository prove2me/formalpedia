-- Prove2me | Theorems.Thm_ResolvingNRM_FRUpper_lemma8_bound_on_b
-- name    : ResolvingNRM.FRUpper.lemma8_bound_on_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:43:50.069816+00:00
-- url     : https://prove2.me/theorems/d506cfa9-35e7-4aba-8795-52f1f960fccd
-- title:
--   Lemma 8 (corrected) — E[(b_l − b_l(t))⁺] ≤ K_l √(Σ_{i<t} 1/(T−i−1)²) with K_l = √(Σ_j a_lj² λ_j)
-- statement:
--   Consider the network revenue management model with Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$, nonnegative consumption matrix $A = (a_{lj})$, initial capacity $C \ge 0$ and an integer horizon $T$. Run the FR policy with any optimal-solution selector, and let $b_l = C_l/T$ and $b_l(t) = C_l(t)/(T - t)$, where $C(t)$ is the remaining capacity at the start of period $t$. Then for every resource $l$ and every period $t$ with $0 \le t \le T - 1$,
--   $$\mathbb{E}\big[(b_l - b_l(t))^+\big] \ \le\ K_l \sqrt{\sum_{i=0}^{t-1} \frac{1}{(T - i - 1)^2}}, \qquad K_l = \sqrt{\sum_{j=1}^n a_{lj}^2 \lambda_j}.$$
--
--   The lemma says the average remaining capacity of FR drifts below its initial value $C/T$ by at most $O(1/\sqrt{T - t})$ in expectation; summed over $t$ through eq. (33), it gives the $O(\sqrt{T})$ term of Proposition 3.
--
--   **Formalization Note.** The printed lemma has $K_l = \sqrt{\sum_j a_{lj}^2 \lambda_j^2}$, which is false: in the proof, eq. (69)–(70) uses $\mathbb{E}[x_j(t)^2] \le \lambda_j^2$ where the conditional variance of the Poisson($x_j(i)$) increment is $x_j(i) \le \lambda_j$. Counterexample to the printed form: one class, one resource, $a = 1$, $\lambda = 0.01$, $C = \lambda T$, $T = 1000$, $t = 2$; an exact computation gives $\mathbb{E}[(b - b(2))^+] \approx 1.96 \cdot 10^{-5}$, above the printed bound $\lambda \sqrt{1/999^2 + 1/998^2} \approx 1.42 \cdot 10^{-5}$ (the corrected bound is $1.42 \cdot 10^{-4}$). The statement uses the corrected $K_l$. The range $t \le T - 1$ is where $b_l(t)$ is defined; it keeps every $T - i - 1 \ge 1$. $\lambda_j > 0$, $r \ge 0$, $a_{lj} \ge 0$, $C \ge 0$ are the model's standing assumptions (p. 7).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Lemma 8, p. 43 (proof pp. 43–44)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- Lemma 8 (Bound on `b_l`), p. 43, with the corrected constant `K_l = √(∑_j a_lj² λ_j)`:
`E[(b_l − b_l(t))⁺] ≤ K_l √(∑_{i=0}^{t-1} 1 / (T − i − 1)²)` for every period `t ≤ T − 1`, where
`b_l = C_l / T` and `b_l(t) = C_l(t) / (T − t)` along FR. -/
theorem lemma8_bound_on_b {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (T t : ℕ) (ht : t + 1 ≤ T) (C : Fin m → ℝ) (hC : 0 ≤ C) (l : Fin m) :
    frStateExp A r lam sel T t (fun c => max (C l / T - c l / ((T : ℝ) - t)) 0) C
      ≤ Kres A lam l *
          Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T : ℝ) - i - 1) ^ 2) := by sorry

end ResolvingNRM.FRUpper
