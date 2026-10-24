-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_lemma_4
-- name    : SampleDrivenOS.Limit.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:20.936984+00:00
-- url     : https://prove2.me/theorems/ab38a856-aba7-4315-ae71-adaaeae0dbe2
-- title:
--   Lemma 4 — a maximal $\alpha$ is at least $\inf_{k\ge1}\frac{1}{1-p^k}\sum_{j=1}^k\int_p^1 t\,q(t,j)\,dt$
-- statement:
--   Let $p\in(0,1)$ and let $(q,\alpha)$ be feasible for SDCLP$_p$, where $q(t,\ell)$ is non-increasing in $\ell$ for every $t\in[p,1]$, and $\alpha$ is maximal for this $q$: $(q,c)$ is infeasible for every $c>\alpha$. Then
--   $$\alpha\ \ge\ \inf_{k\ge1}\frac{1}{1-p^k}\sum_{j=1}^{k}\int_p^1 t\,q(t,j)\,dt. \qquad(13)$$
--
--   The lemma replaces the coefficients $F_k(q)$ in constraint (11) by the simpler quantities $\sum_{j\le k}\int_p^1 t\,q(t,j)\,dt$; the explicit solution of Lemma 6 is built to make every term of this infimum equal.
--
--   **Formalization Note** The infimum is `⨅` over $\{k\in\mathbb N: k\ge1\}$; every term is nonnegative ($q\ge0$ on $[p,1]$), so the infimum of reals is the true one. "Non-increasing in $\ell$" is $q(t,\ell+1)\le q(t,\ell)$ for all $t\in[p,1]$, $\ell\ge1$. $p\in(0,1)$ is the standing assumption of §4.3 ("Fix $p\in(0,1)$", p. 16).
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 16, Lemma 4, (13)

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Lemma 4 (p. 16): if `(q, α)` is feasible for SDCLP_p, `q(t, ℓ)` is non-increasing in
`ℓ` for every `t ∈ [p, 1]`, and `α` is maximal for this `q`, then
`α ≥ inf_{k ≥ 1} (1/(1-p^k)) ∑_{j=1}^{k} ∫_p^1 t q(t, j) dt` (13). -/
theorem lemma_4 (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (q : ℝ → ℕ → ℝ) (α : ℝ)
    (hfeas : IsSDFeasible p q α)
    (hmono : ∀ t ∈ Set.Icc p 1, ∀ ℓ : ℕ, 1 ≤ ℓ → q t (ℓ + 1) ≤ q t ℓ)
    (hmax : ∀ c : ℝ, α < c → ¬ IsSDFeasible p q c) :
    (⨅ k : {k : ℕ // 1 ≤ k}, 1 / (1 - p ^ (k : ℕ)) *
        ∑ j ∈ Finset.Icc 1 (k : ℕ), ∫ t in p..1, t * q t j) ≤ α := by sorry

end SampleDrivenOS.Limit
