-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_display_57
-- name    : PooledRationing.MaxWeighted.display_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:38.537812+00:00
-- url     : https://prove2.me/theorems/c4b3cd4a-37cf-4e69-baf4-3b01778c5a80
-- title:
--   (57), p. 53 — pathwise regret bound of the dual iterates against G(w*)
-- statement:
--   Work in the setting of Theorem 3 (Assumptions 1 and 3, $c$ feasible, $|f|\le K$ on feasible allocations, $R_j\ge0$, $s\le D$ on $P(c,D)$ for $D\ge0$), and let $w\mapsto\varphi_w$ be any selection of optimal solutions of the Max-Weighted-Service problem (16), defined for every $w\ge0$.
--
--   Fix any nonnegative demand path $D^{(1)},D^{(2)},\dots$, a horizon $T\ge1$ and a step $\gamma>0$, and let $w^{(1)}=0,w^{(2)},\dots$ be the iterates (26) of Algorithm 1 along this path with step $\gamma$. Write $\|v\|_2^2=\sum_{j\in N}v_j^2$ (the Euclidean norm) and let $L_t$ be the term (55). Then
--   $$\frac1T\sum_{t=1}^T E_{\tilde D^t}\big[f(y(\varphi_{w^{(t)}},c,\tilde D^t))\big]-G(w^*)\le\frac{1}{2T\gamma}\sum_{t=1}^T\Big\{\|w^{(t)}\|_2^2-\|w^{(t+1)}\|_2^2+\gamma^2\,n(1+C)^2+T\gamma^2L_t\Big\}$$
--   and
--   $$\frac{1}{2T\gamma}\sum_{t=1}^T\Big\{\|w^{(t)}\|_2^2-\|w^{(t+1)}\|_2^2+\gamma^2\,n(1+C)^2+T\gamma^2L_t\Big\}\le\frac{\gamma\,n(1+C)^2}{2}+\frac{\gamma}{2}\sum_{t=1}^TL_t,$$
--   where $E_{\tilde D^t}[\cdot]$ is the expectation over a fresh demand with $w^{(t)}$ fixed and $G(w^*)=\sup_{w\ge0}G(w)$.
--
--   This is the regret inequality of the projected dual subgradient method. Combined with $G(w^*)\le\mathrm{Obj}(11)$ and $\gamma_T\sum_tL_t\to0$, it yields the cost half (27) of Theorem 3.
--
--   **Formalization Note.** The inequality is pathwise: it holds for every demand path, with the expectations $E_{\tilde D^t}$ taken over $F$ at the fixed iterate. The Euclidean norm is written out as a sum of squares (on `Fin n → ℝ` Lean's default norm is the sup norm). Indices are 0-based: the Lean sum over $t=0,\dots,T-1$ is the page's sum over $t=1,\dots,T$, and the Lean iterate at index $t$ is the page's $w^{(t)}$ shifted by one. The step $\gamma$ is any positive constant; the page uses $\gamma=\gamma_T$. Added hypotheses are as in the weak-duality milestone; the demand path is assumed nonnegative, as demand is in the paper.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 53, (55), (57)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm

namespace PooledRationing.MaxWeighted

open MeasureTheory ProbabilityTheory Filter Topology

theorem display_57
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
    (d : ℕ → Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (T : ℕ) (hT : 1 ≤ T) (γ : ℝ) (hγ : 0 < γ) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, PooledRationing.AsymFeas.detCost F f (sel (mwsIter sel β R γ d t))
        - Gstar F f R β P c
      ≤ 1 / (2 * T * γ) * ∑ t ∈ Finset.range T,
          ((∑ j, (mwsIter sel β R γ d t j) ^ 2) - (∑ j, (mwsIter sel β R γ d (t + 1) j) ^ 2)
            + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t) ∧
    1 / (2 * T * γ) * ∑ t ∈ Finset.range T,
          ((∑ j, (mwsIter sel β R γ d t j) ^ 2) - (∑ j, (mwsIter sel β R γ d (t + 1) j) ^ 2)
            + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t)
      ≤ γ * n * (1 + C) ^ 2 / 2 + γ / 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t := by sorry

end PooledRationing.MaxWeighted
