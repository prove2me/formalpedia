-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_theorem_3
-- name    : PooledRationing.MaxWeighted.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:27.121691+00:00
-- url     : https://prove2.me/theorems/5676db4a-9b8e-4294-a84d-ff7af8848224
-- title:
--   Theorem 3, p. 17 — the Max-Weighted-Service policy is almost surely asymptotically optimal
-- statement:
--   A firm serves $n$ customers from $m$ pooled resources at a fixed capacity level $c\ge0$. Demand $\tilde D$ has law $F$ (nonnegative, with a bounded second moment); after demand is seen the firm picks fulfilments and allocations $(s,y)\in P(c,D)$, pays a linear cost $f(y)$, and customer $j$ receives service $R_j(s_j,D_j)\ge0$, with target $\beta_j\in(0,1)$. Assume:
--
--   1. Assumption 1: each $R_j$ is non-decreasing and upper semicontinuous in $s_j$, and each $P(c,D)$ is compact;
--   2. Assumption 3: the support of $\tilde D$ is bounded, and $R_j(s_j,D_j)\le C$ whenever $s_j\le D_j$;
--   3. the capacity level $c$ is feasible, i.e. some randomized policy meets every target (11a).
--
--   Let $\varphi_w$ be the **Max-Weighted-Service policy**: for each $w\ge0$ and each demand $D$, $\varphi_w(c,D)$ is an optimal solution of (16), $\min_{(y,s)\in P(c,D)}f(y)-\sum_jw_jR_j(s_j,D_j)$, ties broken arbitrarily. Let $D^{(1)},D^{(2)},\dots$ be independent samples from $F$, and for each horizon $T$ run Algorithm 1 on $D^{(1)},\dots,D^{(T)}$: $w^{(1)}=0$ and
--   $$w^{(t+1)}_j=\Big[w^{(t)}_j+\gamma_T\big(\beta_j-R_j(s_j(\varphi_{w^{(t)}},c,D^{(t)}),D^{(t)}_j)\big)\Big]^+,\qquad\gamma_T=T^{-(1/2+\epsilon)},\ \epsilon\in(0,1/2).$$
--   Then, almost surely,
--   $$\limsup_{T\to\infty}\frac1T\sum_{t=1}^TE_{\tilde D^t}\big[f(y(\varphi_{w^{(t)}},c,\tilde D^t))\big]\le\mathrm{Obj}(11)\qquad(27)$$
--   and
--   $$\liminf_{T\to\infty}\frac1T\sum_{t=1}^TE_{\tilde D^t}\big[R_j(s_j(\varphi_{w^{(t)}},c,\tilde D^t),\tilde D^t_j)\big]\ge\beta_j\quad\text{for all }j\in N,\qquad(28)$$
--   where $\tilde D^t$ is a fresh copy of the demand, independent of the samples, so each expectation is taken with the iterate $w^{(t)}$ fixed, and $\mathrm{Obj}(11)$ is the optimal value of (11).
--
--   So the randomized policy that adopts $\varphi_{\tilde w_T}$ for an iterate $\tilde w_T$ drawn uniformly from $w^{(1)},\dots,w^{(T)}$ is asymptotically optimal and asymptotically meets every individual service target, without solving the infinite-dimensional problem (11).
--
--   **Formalization Note.** (27) and (28) are stated in the equivalent form "for every $\varepsilon>0$, eventually in $T$" ($\le\mathrm{Obj}(11)+\varepsilon$, resp. $\ge\beta_j-\varepsilon$), with one null set for both inequalities and all $j$. The theorem holds for every tie-breaking selection $w\mapsto\varphi_w$; the selection is assumed jointly measurable in $(w,D)$ so the iterates are random variables. All horizons $T$ read the first $T$ entries of one i.i.d. sequence (the paper does not couple the runs for different $T$). Indices are 0-based: the Lean sum over $t=0,\dots,T-1$ is the page's $\sum_{t=1}^T$. Added hypotheses, none on the page: $R_j\ge0$ and jointly measurable (the page has $R_j:\mathbb R^2_+\to\mathbb R_+$), $s\le D$ on $P(c,D)$ for $D\ge0$, and $|f|\le K$ on feasible allocations, which the paper's proof of Lemma 6 assumes implicitly and which keeps $\mathrm{Obj}(11)$ a genuine infimum.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 17, Theorem 3, (27)–(28), with Algorithm 1 and Assumption 3 (p. 17)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm

namespace PooledRationing.MaxWeighted

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_3
    {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRmono : ∀ j d, Monotone (fun s => R j s d))
    (hRusc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hPcpt : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (B : ℝ) (hA3supp : ∀ᵐ D ∂F, ∀ j, |D j| ≤ B)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (hfeas : PooledRationing.AsymFeas.IsFeasible F R β P c)
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → (Fin n → ℝ)) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (ϵ : ℝ) (hϵ : ϵ ∈ Set.Ioo 0 (1 / 2)) :
    ∀ᵐ ω ∂μ,
      (∀ ε > 0, ∀ᶠ T : ℕ in atTop,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
            PooledRationing.AsymFeas.detCost F f (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t))
          ≤ PooledRationing.AsymFeas.obj11 F f R β P c + ε) ∧
      (∀ j, ∀ ε > 0, ∀ᶠ T : ℕ in atTop,
        β j - ε ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
            PooledRationing.AsymFeas.detService F R (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)) j) := by sorry

end PooledRationing.MaxWeighted
