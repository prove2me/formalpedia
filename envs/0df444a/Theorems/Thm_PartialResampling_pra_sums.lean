-- Prove2me | Theorems.Thm_PartialResampling_pra_sums
-- name    : PartialResampling.pra_sums
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T10:47:08.519907+00:00
-- url     : https://prove2.me/theorems/7c6b114c-5536-4593-8d9c-3f1a53341858
-- title:
--   Partial resampling for sums of random variables (Harris–Srinivasan)
-- statement:
--   Partial resampling for bad events defined by sums (combination of Theorems 3.8 and 4.5 of Harris–Srinivasan).
--
--   Let $X_1,\dots,X_n$ be independent random variables, $X_i$ taking values in a finite set $\Omega_i$ with $\Pr(X_i=\omega)=p_i(\omega)>0$. For each index $t$ of a finite set $T$ let $a_t(i,\omega)\in[0,1]$, and consider the sum $F_t(z)=\sum_i a_t(i,z_i)$. Fix thresholds $\tau_t$, integers $1\le d_t\le\tau_t$ and an inflation factor $\Lambda\ge 1$, and write
--   $$\mu_{t,i}=\Lambda\sum_{\omega}p_i(\omega)a_t(i,\omega),\qquad \mu_t=\sum_i\mu_{t,i},\qquad \Phi_t=\prod_{j=0}^{d_t-1}(\tau_t-j).$$
--   Assume
--   1. for every $t$: $\ \mu_t^{\,d_t}\le \Phi_t/4$;
--   2. for every variable $i$:
--   $$\sum_{t}\frac{d_t\,\mu_{t,i}\,\mu_t^{\,d_t-1}}{\Phi_t}\ \le\ \frac{\log\Lambda}{2}.$$
--
--   Then there is a configuration $z$ with $F_t(z)<\tau_t$ for every $t$.
--
--   The proof uses the fractional hitting set $Q_t(Y)=\frac{d_t!}{\Phi_t}\prod_{(i,\omega)\in Y}a_t(i,\omega)$ on atomic sets with $|Y|=d_t$ (Theorem 4.5), the symmetric-polynomial bounds of Propositions 4.2–4.3, and the $\lambda$-parametrised criterion of Theorem 3.8 with $\lambda_{i,\omega}=\Lambda p_i(\omega)$. Choosing $\Lambda=1+\varepsilon$ and $d_t\approx\tau_t-\mu_t$ yields Chernoff-type bounds that hold simultaneously for all $t$ and do not depend on the number of events or variables (column-sparse assignment packing, Theorem 4.7).
-- source:
--   D. G. Harris and A. Srinivasan, The Moser–Tardos framework with partial resampling, J. ACM 66(5):36 (2019), arXiv:1406.5943, Theorem 3.8 (p. 15), Propositions 4.2–4.3 and Theorem 4.5 (pp. 16–17).

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

namespace PartialResampling

theorem pra_sums {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    (Ω : I → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (a : T → ∀ i, Ω i → ℝ) (ha : ∀ t i ω, 0 ≤ a t i ω ∧ a t i ω ≤ 1)
    (τ : T → ℝ) (d : T → ℕ) (hd : ∀ t, 1 ≤ d t ∧ (d t : ℝ) ≤ τ t)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hS : ∀ t, (Λ * ∑ i, ∑ ω, p i ω * a t i ω) ^ d t ≤
      (∏ j ∈ Finset.range (d t), (τ t - j)) / 4)
    (hG : ∀ i, ∑ t, (d t : ℝ) * (Λ * ∑ ω, p i ω * a t i ω) *
        (Λ * ∑ u, ∑ ω, p u ω * a t u ω) ^ (d t - 1) / ∏ j ∈ Finset.range (d t), (τ t - j) ≤
      Real.log Λ / 2) :
    ∃ z : ∀ i, Ω i, ∀ t, ∑ i, a t i (z i) < τ t := by sorry

end PartialResampling
