-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_nonneg_process_not_tendsto_zero
-- name    : StochApproxDyn.WeakAPT.Supplement.nonneg_process_not_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:18:29.219783+00:00
-- url     : https://prove2.me/theorems/6b19f073-c0f8-45d0-bc61-1144bf775df7
-- title:
--   Lemma 9.6 — a nonnegative process with nonnegative drift above ε_n and excited squares does not converge to 0 (Pemantle)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_n)$. Let $(S_n)$ be a nonnegative stochastic process, $S_n=S_0+\sum_{i=1}^nX_i$, where $S_0$ is $\mathcal F_0$-measurable and $X_n$ is $\mathcal F_n$-measurable. Let $(\gamma_n)$ be positive numbers with $\sum_n\gamma_n^2<\infty$ and let $\alpha_n=\sum_{i=n+1}^\infty\gamma_i^2$. Assume there exist a sequence $0\le\varepsilon_n=o(\sqrt{\alpha_n})$, constants $a_1>0$, $a_2>0$ and an integer $N_0$ such that for all $n\ge N_0$:
--
--   1. $|X_n|=o(\sqrt{\alpha_n})$;
--   2. $\mathbf 1_{\{S_n>\varepsilon_n\}}E(X_{n+1}\mid\mathcal F_n)\ge0$;
--   3. $E(S_{n+1}^2-S_n^2\mid\mathcal F_n)\ge a_1\gamma_{n+1}^2$;
--   4. $E(X_{n+1}^2\mid\mathcal F_n)\le a_2\gamma_{n+1}^2$.
--
--   Then
--
--   $$P\Big(\lim_{n\to\infty}S_n=0\Big)=0.$$
--
--   This is the probabilistic core of Theorem 9.1 in the case $\sum\gamma_n^2<\infty$, adapted from Pemantle (1992, Lemma 5.5).
--
--   **Formalization Note** The $o(\cdot)$ conditions are genuine limits: for every $c>0$, eventually $\varepsilon_n\le c\sqrt{\alpha_n}$ and $|X_n(\omega)|\le c\sqrt{\alpha_n}$ for every $\omega$. Since $S_n$ is $\mathcal F_n$-measurable, $E(S_{n+1}^2-S_n^2\mid\mathcal F_n)=2S_nE(X_{n+1}\mid\mathcal F_n)+E(X_{n+1}^2\mid\mathcal F_n)$, and condition 3 is written in that form, which needs no integrability of $S_n$.
--
--   Differences from the source:
--   - reading: "$\{S_n\}$ a stochastic process … $X_n$ is $\mathcal F_n$ measurable" → $S_0$ is also $\mathcal F_0$-measurable; reason: the conditions given $\mathcal F_n$ treat $S_n$ as known.
--   - reading: "(i) $|X_n|=o(\sqrt{\alpha_n})$" → uniformly in $\omega$; reason: the proof uses the deterministic bound $|X_n|\le\sqrt{b_1\alpha_n}$ for all $n$ beyond a fixed $N_0$.
--   - encoding: $E(S_{n+1}^2-S_n^2\mid\mathcal F_n)$ → $2S_nE(X_{n+1}\mid\mathcal F_n)+E(X_{n+1}^2\mid\mathcal F_n)$; reason: equal for $\mathcal F_n$-measurable $S_n$, and avoids Lean's value $0$ for the conditional expectation of a non-integrable variable.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 55–56, Lemma 9.6

import Mathlib

open MeasureTheory Filter

namespace StochApproxDyn.WeakAPT.Supplement

/-- Lemma 9.6 (Benaïm 1999, pp. 55–56; adapted from Pemantle 1992, Lemma 5.5). Let `{S_n}` be a
nonnegative stochastic process, `S_n = S_0 + ∑_{i=1}^n X_i`, where `X_n` is `ℱ_n`-measurable (and
`S_0` is `ℱ_0`-measurable). Let `{γ_n}` be a sequence of positive numbers with
`∑_n γ_n² < ∞` and let `α_n = ∑_{i=n+1}^∞ γ_i²`. Assume there exist a sequence
`0 ≤ ε_n = o(√α_n)`, constants `a₁ > 0`, `a₂ > 0` and an integer `N₀` such that for all
`n ≥ N₀`:
(i) `|X_n| = o(√α_n)`;
(ii) `1_{S_n > ε_n} E(X_{n+1} | ℱ_n) ≥ 0`;
(iii) `E(S_{n+1}² − S_n² | ℱ_n) ≥ a₁ γ_{n+1}²`;
(iv) `E(X_{n+1}² | ℱ_n) ≤ a₂ γ_{n+1}²`.
Then `P(lim_{n → ∞} S_n = 0) = 0`.

Clause (i) is read uniformly in `ω` (the deterministic bound `|X_n| ≤ c_n` with `c_n = o(√α_n)`
used in the proof). In (iii) the conditional expectation of `S_{n+1}² − S_n² = 2 S_n X_{n+1} +
X_{n+1}²` is written as `2 S_n E(X_{n+1} | ℱ_n) + E(X_{n+1}² | ℱ_n)`, its value for the
`ℱ_n`-measurable `S_n` (this needs no integrability of `S_n`). -/
theorem nonneg_process_not_tendsto_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (S X : ℕ → Ω → ℝ) (hS0 : StronglyMeasurable[ℱ 0] (S 0))
    (hX : ∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (X (n + 1)))
    (hSX : ∀ n ω, S (n + 1) ω = S n ω + X (n + 1) ω) (hSnn : ∀ n ω, 0 ≤ S n ω)
    (γ : ℕ → ℝ) (hγ : ∀ n : ℕ, 0 < γ (n + 1)) (hγsum : Summable (fun n : ℕ => γ (n + 1) ^ 2))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n)
    (hεo : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ε n ≤ c * Real.sqrt (∑' i : ℕ, γ (n + 1 + i) ^ 2))
    (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (N₀ : ℕ)
    (h_i : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ ω,
      |X n ω| ≤ c * Real.sqrt (∑' i : ℕ, γ (n + 1 + i) ^ 2))
    (h_ii : ∀ n, N₀ ≤ n → ∀ᵐ ω ∂P, ε n < S n ω → 0 ≤ (P[X (n + 1) | ℱ n]) ω)
    (h_iii : ∀ n, N₀ ≤ n → ∀ᵐ ω ∂P,
      a₁ * γ (n + 1) ^ 2 ≤ 2 * S n ω * (P[X (n + 1) | ℱ n]) ω +
        (P[fun ω => X (n + 1) ω ^ 2 | ℱ n]) ω)
    (h_iv : ∀ n, N₀ ≤ n → ∀ᵐ ω ∂P,
      (P[fun ω => X (n + 1) ω ^ 2 | ℱ n]) ω ≤ a₂ * γ (n + 1) ^ 2) :
    P {ω | Tendsto (fun n => S n ω) atTop (nhds 0)} = 0 := by sorry

end StochApproxDyn.WeakAPT.Supplement
