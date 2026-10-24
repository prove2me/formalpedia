-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_theorem_1
-- name    : SecretaryPred.LearnedDynkin.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:47.002114+00:00
-- url     : https://prove2.me/theorems/781c869b-f923-44fd-945f-9efa3922f4d3
-- title:
--   Theorem 1, p. 6 — learned Dynkin with θ = 0.646, τ = 0.313 is max{0.215, (1−ϵ)/(1+ϵ)}-competitive
-- statement:
--   **Theorem 1** (Fujii and Yoshida, p. 6). Consider the classical secretary problem with predictions in the continuous-time model: $n$ candidates with values $v(i)\ge 0$ and predictions $\hat v(i)\ge 0$ arrive at independent Uniform$[0,1]$ times, and Algorithm 1 (learned Dynkin) is run with threshold $\theta=0.646$, time $\tau=0.313$, and any maximizer $\hat\imath$ of $\hat v$. Let $\mathbb E[\mathrm{ALG}]$ be the expected value of the hired candidate ($0$ if nobody is hired). Then:
--   1. $\mathbb E[\mathrm{ALG}]\ge 0.215\cdot\max_i v(i)$;
--   2. for every $\epsilon\ge 0$ with $(1-\epsilon)v(i)\le\hat v(i)\le(1+\epsilon)v(i)$ for all $i$,
--
--   $$\mathbb E[\mathrm{ALG}]\;\ge\;\frac{1-\epsilon}{1+\epsilon}\cdot\max_i v(i).$$
--
--   Together, with $\epsilon=\max_i|1-\hat v(i)/v(i)|$ the largest multiplicative prediction error, Algorithm 1 is $\max\{0.215,(1-\epsilon)/(1+\epsilon)\}$-competitive.
--
--   The theorem says that one algorithm is simultaneously near-optimal when the predictions are accurate (the ratio tends to $1$ as $\epsilon\to 0$) and robust when they are not (a constant $0.215$ whatever the predictions are). Without predictions the best possible ratio is $1/e$, attained by Dynkin's rule.
--
--   **Formalization Note** Candidates are `Fin n` (0-based). $\mathbb E[\mathrm{ALG}]$ is `expectedValue 0.646 0.313 v v̂ ı̂`, the integral of the value of the run of Algorithm 1 against the uniform law on $[0,1]^n$; the run is encoded in the definitions file (lines 4–9 of Algorithm 1, the strict tie-broken best-so-far test). The benchmark $\max_i v(i)$ is written as $\alpha\,v(j)\le\mathbb E[\mathrm{ALG}]$ for every $j$, and the error condition as $|v(i)-\hat v(i)|\le\epsilon\,v(i)$.
--
--   Differences from the source:
--   - reading: line 8 of Algorithm 1: 'i is the best so far', with ties not addressed; i∗ ∈ argmax v → i beats every earlier arrival in the strict order 'larger value, then smaller index' (Beats); istar is the top candidate of that order; reason: both untied readings make Theorem 1 false: strictly larger value fails for n ≥ 5 candidates all with v = 1 and exact predictions except v̂(ı̂) = 10 (P(hire) ≤ 1/n < 0.215); weakly larger value fails for i∗ with v = v̂ = 1, ı̂ with v = δ, v̂ = 10 and n − 2 fillers with v = v̂ = δ (ratio → δ as n → ∞); for distinct values the order is the source's
--   - generalization: ϵ = max_i |1 − v̂(i)/v(i)|, the competitive ratio (1 − ϵ)/(1 + ϵ) → for every ε ≥ 0 with |v(i) − v̂(i)| ≤ ε·v(i) for all i, (1 − ε)/(1 + ε)·v(j) ≤ E[ALG]; reason: when all v(i) > 0 the source's ϵ is the least such ε and (1 − ε)/(1 + ε) decreases in ε, so the clause at that ε is the source's; the Lean clause also covers v(i) = 0, where the source's ϵ is undefined
--   - encoding: α-competitive with α = max{0.215, (1 − ϵ)/(1 + ϵ)}: E[ALG] ≥ α·max_i v(i) → two clauses, ∀ j, 0.215·v(j) ≤ E[ALG] and ∀ j, (1 − ε)/(1 + ε)·v(j) ≤ E[ALG]; reason: max{a, b}·OPT ≤ E iff a·OPT ≤ E and b·OPT ≤ E when OPT ≥ 0, and ∀ j, α·v(j) ≤ E is α·max_i v(i) ≤ E since the maximum is attained (a negative α gives a true clause, as E ≥ 0)
--   - encoding: ı̂ ∈ argmax v̂ (line 1, any choice) → ihat is any index with v̂(j) ≤ v̂(ihat) for all j, universally quantified; reason: line 1 allows any maximizer, so the theorem is claimed for each
--   - encoding: |1 − v̂(i)/v(i)| > θ (line 4 and the set M, p. 6) → θ·v(i) < |v(i) − v̂(i)| (Deviates); reason: identical when v(i) > 0; avoids Lean's x/0 = 0, and for v(i) = 0 a candidate deviates iff v̂(i) ≠ 0
--   - encoding: candidates N = [n] interviewed in random order, arrival times iid Uniform[0, 1] (§2.1), exactly one hire → candidates Fin n (0-based), t uniform on the cube [0, 1]^n (arrivalLaw n), the mode at i is Secretary iff some deviating j has t_j ≤ t_i, and algValue sums the values of all candidates that are first to stop; reason: the run differs from the source's single-hire run only on the null set of arrival vectors with two equal times
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, p. 6, Theorem 1 (with Algorithm 1, p. 6, and §2, §2.1, pp. 4–5)

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem theorem_1 (n : ℕ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat) :
    (∀ j, 0.215 * v j ≤ expectedValue 0.646 0.313 v vhat ihat) ∧
      ∀ eps : ℝ, 0 ≤ eps → (∀ i, |v i - vhat i| ≤ eps * v i) →
        ∀ j, (1 - eps) / (1 + eps) * v j ≤ expectedValue 0.646 0.313 v vhat ihat := by sorry

end SecretaryPred.LearnedDynkin
