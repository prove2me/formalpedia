-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_weak_duality
-- name    : PooledRationing.MaxWeighted.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:54.054284+00:00
-- url     : https://prove2.me/theorems/b60a1d27-6ae6-4ae5-82a2-31fe872e8d8f
-- title:
--   Proof of Theorem 3, p. 52, and of Lemma 6, p. 54 — weak duality: G(w) = Σ wⱼβⱼ + E[f(y(φ_w))] − Σ wⱼE[Rⱼ(sⱼ(φ_w))] ≤ Obj(11) for every w ≥ 0
-- statement:
--   Consider the pooled-resource model with demand law $F$, feasible sets $P(c,D)$, linear cost $f$, service measures $R_j$ and targets $\beta_j\in(0,1)$, under Assumption 1 (each $R_j$ non-decreasing and upper semicontinuous in $s_j$; each $P(c,D)$ compact) and Assumption 3 (bounded demand; $R_j(s_j,D_j)\le C$ whenever $s_j\le D_j$). Assume moreover that $0\le R_j$, that every feasible solution satisfies $s\le D$ for nonnegative $D$, and that $|f(y)|\le K$ on $P(c,D)$ for $F$-almost every $D$.
--
--   Suppose the capacity level $c$ is feasible. Let $w\ge0$ and let $\varphi_w$ be any deterministic policy that solves the Max-Weighted-Service problem (16) at $w$ for every demand vector $D$. Then
--   $$\sum_{j\in N}w_j\beta_j+E_{\tilde D}\big[f(y(\varphi_w,c,\tilde D))\big]-\sum_{j\in N}w_j\,E_{\tilde D}\big[R_j(s_j(\varphi_w,c,\tilde D),\tilde D_j)\big]\le\mathrm{Obj}(11).$$
--
--   The left-hand side is $G(w)$ of (25), so this is weak duality between (11) and its Lagrangian dual. In the proof of Lemma 6 it bounds the dual iterates, and through $G(w^*)\le\mathrm{Obj}(11)$ it reduces (27) to a regret bound.
--
--   **Formalization Note.** The page states the inequality as $G(w^*)\le\mathrm{Obj}(11)$ with $G(w^*)=\max_{w\ge0}G(w)$ (p. 52) and at $w=w^{(t)}$ (p. 54); it is stated here for every $w\ge0$, which is equivalent to the first and contains the second as an instance. Added hypotheses: $R_j\ge0$ (the page has $R_j:\mathbb R^2_+\to\mathbb R_+$), joint measurability of $R_j$, $s\le D$ on $P(c,D)$ for $D\ge0$ (part of every model on pp. 3–4; Assumption 3's bound is stated for $s_j\le D_j$), and the bound $|f|\le K$ on feasible allocations, which the paper's proof of Lemma 6 assumes implicitly (its constant $\hat C_2$) and which makes $\mathrm{Obj}(11)$ a genuine infimum. The standing assumptions of §1.1 (nonnegative demand with bounded second moment, $c\ge0$) are kept.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 52, proof of Theorem 3 ('From weak duality (Shapiro, 2001), it holds that G(w*) ≤ Obj (11)'), and p. 54, proof of Lemma 6, display after 'Also, from weak duality'

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

namespace PooledRationing.MaxWeighted

open MeasureTheory

theorem weak_duality
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
    (w : Fin n → ℝ) (hw : 0 ≤ w) (φw : PooledRationing.AsymFeas.DetPolicy P c)
    (hφw : ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) (φw.toFun D)) :
    ∑ j, w j * β j + PooledRationing.AsymFeas.detCost F f φw - ∑ j, w j * PooledRationing.AsymFeas.detService F R φw j
      ≤ PooledRationing.AsymFeas.obj11 F f R β P c := by sorry

end PooledRationing.MaxWeighted
