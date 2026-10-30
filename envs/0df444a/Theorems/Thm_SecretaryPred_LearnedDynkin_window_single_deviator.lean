-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_window_single_deviator
-- name    : SecretaryPred.LearnedDynkin.window_single_deviator
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T12:15:29.102527+00:00
-- url     : https://prove2.me/theorems/d8c355c3-e4ae-4506-b9f3-16990cd0001e
-- title:
--   Theorem 1, p. 6 — window θ < ε: single-deviator cases (ii)/(iv)/(vi) with m = 1 achieve (1−ε)/(1+ε)
-- statement:
--   **Setting.** As in Theorem 1 of Fujii and Yoshida (p. 6): $n$ candidates with values $v(i)\ge 0$ and predictions $\hat v(i)\ge 0$ arrive at independent Uniform$[0,1]$ times, Algorithm 1 (learned Dynkin) runs with $\theta=0.646$, $\tau=0.313$ and a maximizer $\hat\imath$ of $\hat v$, and $\mathbb E[\mathrm{ALG}]$ is the expected value of the hired candidate. Let $i^*$ be the top candidate (largest value, ties broken by smaller index), and $M=\{i : |v(i)-\hat v(i)|>\theta\, v(i)\}$ the set of deviating candidates.
--
--   **Statement.** Suppose exactly one candidate deviates, $|M|=1$, and $i^*\notin M$. Let $\epsilon>\theta$ satisfy $|v(i)-\hat v(i)|\le\epsilon\,v(i)$ for every $i$. Then
--   $$\mathbb E[\mathrm{ALG}]\;\ge\;\frac{1-\epsilon}{1+\epsilon}\,v(i^*).$$
--
--   **Why this lemma is needed.** Theorem 1 claims the competitive ratio $\max\{0.215,(1-\epsilon)/(1+\epsilon)\}$. The paper's proof covers $\epsilon\le\theta$ (then $M=\emptyset$ and $\hat\imath$ is hired) and shows ratio $\ge 0.215$ otherwise. But for $\epsilon$ in the window $\theta<\epsilon<\epsilon_0\approx 0.64609$ one has
--   $$0.215<\frac{1-\epsilon}{1+\epsilon}<\frac{1-\theta}{1+\theta}=\frac{177}{823}\approx 0.2150668,$$
--   and the paper's bounds for case (iv) with $m=1$ (namely $\tau(1-\tau)=0.215031$) and case (vi) with $m=1$ (namely $\approx 0.2150489$) fall below $(1-\epsilon)/(1+\epsilon)$ there. All other case bounds of the paper exceed $(1-\theta)/(1+\theta)$. This lemma isolates exactly the uncovered situation: cases (ii), (iv), (vi) of the proof with $m=|M|=1$, under the accuracy hypothesis with $\epsilon>\theta$. Without the accuracy hypothesis the bound $(1-\theta)/(1+\theta)$ can fail in case (iv) (take $\hat\imath$ second-best with tiny value: the ratio tends to $\tau(1-\tau)$), so the hypothesis $|v(i)-\hat v(i)|\le\epsilon v(i)$, which forces $v(\hat\imath)\ge\frac{1-\epsilon}{1+\epsilon}v(i^*)$, is essential. Simulations indicate the true ratio in these cases is at least about $0.23$.
--
--   **Formalization.** `Deviates`, `Mset`, `Beats`, `expectedValue` are from the definitions file `SecretaryPred_LearnedDynkin_Setting` (ties broken by `Beats`, $\mathbb E[\mathrm{ALG}]$ an integral against the uniform law on $[0,1]^n$).
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, p. 6, Theorem 1 (eps-clause for ε > θ), proof cases (iv) and (vi) on pp. 8–10 specialized to m = |M| = 1

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem window_single_deviator (n : ℕ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j)
    (hstarM : ¬ Deviates 0.646 v vhat istar) (hM : (Mset 0.646 v vhat).card = 1)
    (eps : ℝ) (heps : 0.646 < eps) (herr : ∀ i, |v i - vhat i| ≤ eps * v i) :
    (1 - eps) / (1 + eps) * v istar ≤ expectedValue 0.646 0.313 v vhat ihat := by sorry

end SecretaryPred.LearnedDynkin
