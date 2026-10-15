-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_eq_7_solves_eq5_eq6
-- name    : SampleDrivenOS.Structure.eq_7_solves_eq5_eq6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:29.439928+00:00
-- url     : https://prove2.me/theorems/287f8868-1793-418a-a0da-634988b6b71f
-- title:
--   Proof of Theorem 2, p. 10 — the threshold function (7) satisfies equations (5) and (6)
-- statement:
--   Let $0\le p<1$ and let $(t_i)_{i\ge0}$ be a non-decreasing sequence in $[p,1]$ with $t_0=p$ and $t_1>0$; put $T_i=\prod_{j=1}^{i}t_j$. Let $q$ have the threshold form (7) on $[p,1)$: for $\ell\ge1$ and $\tau\in[p,1)$,
--   $$q(\tau,\ell)=\begin{cases}T_i/\tau^{i+1}&\text{if }\tau\in[t_i,t_{i+1}),\ \ell\le i,\\ 0&\text{else.}\end{cases}$$
--   Then for every $\ell\ge1$ and $\tau\in[p,1)$:
--   1. (5) if $\tau\ge t_\ell$, and either $\tau<t_i$ for some $i$ or $T_m/t_m^m\to0$ as $m\to\infty$, then $\tau\,q(\tau,\ell)+\int_p^\tau\sum_{s\ge1}q(\sigma,s)\,d\sigma=1$;
--   2. (6) if $\tau<t_\ell$, then $q(\tau,\ell)=0$.
--
--   This is the existence half of the second part of the proof of Theorem 2: the explicit function (7) solves (5)–(6), so by uniqueness the improved solution has the threshold form.
--
--   **Formalization Note** Two conditions left implicit on the page are made explicit. (i) $t_1>0$: with $p=0$ and $t_1=0$ every $T_i$ vanishes and (5) fails; for $p>0$ it is automatic. (ii) On $[t_m,t_{m+1})$ the cumulative mass of (7) is $1-T_m/\tau^m$, so at $L=\lim_i t_i$ it equals $1-\lim_m T_m/t_m^m$. Hence (5) holds for every $\tau<L$, i.e. when $\tau<t_i$ for some $i$; for $L\le\tau<1$, where (7) vanishes, it holds exactly when $T_m/t_m^m\to0$. The page's claim fails otherwise (e.g. $t_j=L(1-2^{-j})$ with $L<1$, where $T_m/t_m^m\to\prod_j(1-2^{-j})\approx0.29$), so (5) is claimed under the disjunction of these two conditions. In Theorem 2 itself the second condition is automatic, because feasibility of the constructed solution forces the cumulative mass to reach $1$ at $L$. The cumulative mass is the extended-real lower integral of the series.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 10 (PDF p. 11), proof of Theorem 2, verification that (7) satisfies (5)–(6)

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set Filter Topology

namespace SampleDrivenOS.Structure

theorem eq_7_solves_eq5_eq6 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ → ℝ)
    (ht : Monotone t) (ht0 : t 0 = p) (htI : ∀ i : ℕ, t i ∈ Icc p 1) (ht1 : 0 < t 1)
    (q : ℝ → ℕ → ℝ) (hq : IsThresholdForm p t q) :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ τ ∈ Ico p 1,
      (t ℓ ≤ τ →
        ((∃ i : ℕ, τ < t i) ∨
          Tendsto (fun m : ℕ => thresholdProd t m / t m ^ m) atTop (𝓝 0)) →
        ENNReal.ofReal (τ * q τ ℓ) + cumMass p q τ = 1) ∧
      (τ < t ℓ → q τ ℓ = 0) := by sorry

end SampleDrivenOS.Structure
