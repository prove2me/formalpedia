-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_lemma_5
-- name    : SampleDrivenOS.Limit.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:17.1517+00:00
-- url     : https://prove2.me/theorems/58dfc68b-a35f-4684-b37c-35962dd6808c
-- title:
--   Lemma 5 — for thresholds $p=t_1\le t_2\le\cdots\le1$, the system (14) is equivalent to (15)–(16)
-- statement:
--   Let $p\in(0,1)$, let $p=t_1\le t_2\le\cdots\le1$, let $T_i=\prod_{j=1}^i t_j$, and let $q$ be the threshold stopping rule (12) built from these times. Put $\mu_k=\sum_{i=k}^{\infty}\frac{T_i}{t_i^{i-1}}\cdot\frac{1}{(i-2)(i-1)}$ for $k\ge3$. For every real $\alpha$, the system
--   $$\alpha=\frac{1}{1-p^k}\sum_{j=1}^{k}\int_p^1 t\,q(t,j)\,dt\qquad\forall k\ge1 \qquad(14)$$
--   holds if and only if
--   $$\alpha(1-p)=p\ln\frac{t_2}{p}+p-\mu_3 \qquad(15)$$
--   and
--   $$\alpha(1-p)p^{k-1}=\frac{1}{k-1}\cdot\frac{T_k}{t_k^{k-1}}-\mu_{k+1}\qquad\forall k\ge2. \qquad(16)$$
--
--   The lemma turns the requirement that every term of Lemma 4's infimum equals $\alpha$ into explicit equations on the thresholds.
--
--   **Formalization Note** The threshold form uses the half-open intervals $[t_i,t_{i+1})$ (see the definition file); the paper prints closed intervals, which differ only at the countably many $t_i$. The time variable inside the integrals is written $\tau$ because $t$ names the threshold sequence. The value $t_0$ of the sequence is unconstrained and does not affect $q(\cdot,\ell)$ for $\ell\ge1$.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 16, Lemma 5, (12), (14)–(16)

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Lemma 5 (p. 16): for `q` of the form (12) with thresholds `p = t_1 ≤ t_2 ≤ ⋯ ≤ 1`, the
system (14) `α = (1/(1-p^k)) ∑_{j=1}^{k} ∫_p^1 t q(t, j) dt` (all `k ≥ 1`) is equivalent to (15)
`α(1-p) = p ln(t_2/p) + p - µ_3` together with (16)
`α(1-p)p^{k-1} = (1/(k-1)) T_k / t_k^{k-1} - µ_{k+1}` (all `k ≥ 2`). -/
theorem lemma_5 (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (t : ℕ → ℝ) (ht1 : t 1 = p)
    (hmono : ∀ i : ℕ, 1 ≤ i → t i ≤ t (i + 1)) (hle : ∀ i : ℕ, 1 ≤ i → t i ≤ 1) (α : ℝ) :
    (∀ k : ℕ, 1 ≤ k →
        α = 1 / (1 - p ^ k) * ∑ j ∈ Finset.Icc 1 k, ∫ τ in p..1, τ * thresholdQ t τ j) ↔
      (α * (1 - p) = p * Real.log (t 2 / p) + p - mu t 3 ∧
        ∀ k : ℕ, 2 ≤ k → α * (1 - p) * p ^ (k - 1) =
          1 / ((k : ℝ) - 1) * (SampleDrivenOS.Structure.thresholdProd t k / t k ^ (k - 1)) - mu t (k + 1)) := by sorry

end SampleDrivenOS.Limit
