-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_case_M_empty
-- name    : SecretaryPred.LearnedDynkin.case_M_empty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:27.217369+00:00
-- url     : https://prove2.me/theorems/00f219b6-b74b-45af-aad8-eab4a7b6af30
-- title:
--   Proof of Theorem 1, case M = ∅ and (1), pp. 6–7 — if no candidate deviates, Algorithm 1 hires ı̂ and v(ı̂) ≥ (1−ϵ)/(1+ϵ)·v(i)
-- statement:
--   Let $n$ candidates have values $v(i)\ge 0$ and predictions $\hat v(i)\ge 0$, let $\hat\imath$ be any maximizer of $\hat v$, and run Algorithm 1 (learned Dynkin) with any threshold $\theta$ and time $\tau$. Suppose no candidate deviates, i.e. $M=\{i : |1-\hat v(i)/v(i)|>\theta\}=\emptyset$. Then:
--   1. on every arrival vector the algorithm stays in Prediction mode and hires $\hat\imath$, so its value is $v(\hat\imath)$;
--   2. hence $\mathbb E[\mathrm{ALG}]=v(\hat\imath)$;
--   3. inequality (1): for every $\epsilon\ge 0$ with $(1-\epsilon)v(i)\le\hat v(i)\le(1+\epsilon)v(i)$ for all $i$, and every candidate $j$,
--
--   $$v(\hat\imath)\;\ge\;\frac{1}{1+\epsilon}\hat v(\hat\imath)\;\ge\;\frac{1}{1+\epsilon}\hat v(j)\;\ge\;\frac{1-\epsilon}{1+\epsilon}\,v(j).$$
--
--   This is the first half of the proof of Theorem 1: when the predictions are accurate up to $\theta$, the algorithm follows them and is $(1-\epsilon)/(1+\epsilon)$-competitive.
--
--   **Formalization Note** Candidates are `Fin n` (0-based). The prediction-error condition is written $|v(i)-\hat v(i)|\le\epsilon\,v(i)$.
--
--   Differences from the source:
--   - generalization: θ = 0.646, τ = 0.313 → any θ and τ; reason: the case M = ∅ never uses θ or τ beyond the definition of M; it specializes to the source's values
--   - generalization: (1) for the optimal candidate i∗ → (1) for every candidate j; reason: i∗ is one of the j; the chain of (1) uses nothing about i∗
--   - generalization: ϵ = max_i |1 − v̂(i)/v(i)| → every ε ≥ 0 with |v(i) − v̂(i)| ≤ ε·v(i) for all i; reason: when all v(i) > 0 the source's ϵ is one such ε; the Lean clause also covers v(i) = 0, where the source's ϵ is undefined
--   - encoding: the algorithm hires ı̂ → algValue = v(ı̂) on every arrival vector t, and expectedValue = v(ı̂); reason: the value of the run and its expectation when ı̂ is the hire
--   - encoding: |1 − v̂(i)/v(i)| > θ (line 4 and the set M, p. 6) → θ·v(i) < |v(i) − v̂(i)| (Deviates); reason: identical when v(i) > 0; avoids Lean's x/0 = 0, and for v(i) = 0 a candidate deviates iff v̂(i) ≠ 0
--   - encoding: candidates N = [n] interviewed in random order, arrival times iid Uniform[0, 1] (§2.1), exactly one hire → candidates Fin n (0-based), t uniform on the cube [0, 1]^n (arrivalLaw n), the mode at i is Secretary iff some deviating j has t_j ≤ t_i, and algValue sums the values of all candidates that are first to stop; reason: the run differs from the source's single-hire run only on the null set of arrival vectors with two equal times
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, pp. 6–7, proof of Theorem 1, case M = ∅, inequality (1)

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem case_M_empty (n : ℕ) (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (hM : Mset theta v vhat = ∅) :
    (∀ t : Fin n → ℝ, algValue theta tau v vhat ihat t = v ihat) ∧
      expectedValue theta tau v vhat ihat = v ihat ∧
      ∀ eps : ℝ, 0 ≤ eps → (∀ i, |v i - vhat i| ≤ eps * v i) →
        ∀ j, (1 - eps) / (1 + eps) * v j ≤ v ihat := by sorry

end SecretaryPred.LearnedDynkin
