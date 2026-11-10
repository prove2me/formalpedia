-- Prove2me | Theorems.Thm_PrefixVR_eq_26
-- name    : PrefixVR.eq_26
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:37:26.641963+00:00
-- url     : https://prove2.me/theorems/7fd6dd08-ba77-45bb-8c40-7f3b192f55ff
-- title:
--   Eq. (26) — Assumption 1 implies Assumption 3 with $L_f=L$ and $\delta=L$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ satisfy **Assumption 1**: each $f_i$ is continuously differentiable with $\nabla f_i=g_i$, and
--   $$
--   \|\nabla f_i(x)-\nabla f_i(y)\|\le L\|x-y\|\qquad\text{for all }x,y\in\mathbb R^d,\ i\in[n],
--   $$
--   with $L>0$. Then **Assumption 3 holds with $L_f=L$ and $\delta=L$**: the average $f=\frac1n\sum_i f_i$ is $L$-smooth, and
--   $$
--   \frac1n\sum_{i=1}^n\|\nabla f_i(x)-\nabla f_i(y)-\nabla f(x)+\nabla f(y)\|^2\le L^2\|x-y\|^2\qquad\text{for all }x,y .
--   $$
--
--   This lets every result proved under Assumption 3 (Lemma 1 and the descent calculation) be used under Assumption 1 with $L_f=\delta=L$, as in the proof of Theorem 1.
--
--   **Formalization Note** Assumption 1 for component $i$ is the published `IsBetaSmooth (fi i) (g i) L` (gradient $g_i$ everywhere, $L$-Lipschitz) together with $0<L$; a Lipschitz gradient is continuous, so this is "continuously differentiable and $L$-smooth".
--
--   Differences from the source:
--   - encoding: Assumption 1: fᵢ continuously differentiable and L-smooth, L > 0 → 0 < L and IsBetaSmooth (fi i) (g i) L for every i; reason: a Lipschitz gradient is continuous, so the same functions qualify
--   - encoding: Assumption 3 holds with L_f = L and δ = L → Assumption3 fi g L L, which also records that each fi i has gradient g i; reason: the gradients ∇fᵢ named in (2) exist under Assumption 1
--   - encoding: [n] → Fin n; reason: Lean convention
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. A, "Relation to component smoothness", Eq. (26), p.13 (PDF p.13); also §4, p.7

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_Assumption3

namespace PrefixVR

/-- **Assumption 1 implies Assumption 3 with `L_f = L` and `δ = L`.** Jiang, Wang, Yang, Li, Zhang
(manuscript, sha256 ed33106a…), App. A, "Relation to component smoothness", Eq. (26), p.13
(also §4, p.7): "Thus Assumption 3 holds with L_f = L and δ = L."

Assumption 1 (p.4): each `fᵢ` is continuously differentiable and `L`-smooth,
`‖∇fᵢ(x) − ∇fᵢ(y)‖ ≤ L‖x − y‖`, `L > 0`.

**Formalization Note.** Assumption 1 for component `i` is `IsBetaSmooth (fi i) (g i) L` (the
published `ConvexOptAlg.SmoothGD.IsBetaSmooth`: `fi i` has gradient `g i x` at every `x` and `g i`
is `L`-Lipschitz; a Lipschitz gradient is continuous, so this is "continuously differentiable and
L-smooth") together with `0 < L`. -/
theorem eq_26 {n d : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 0 < L)
    (hA1 : ∀ i, ConvexOptAlg.SmoothGD.IsBetaSmooth (fi i) (g i) L) :
    Assumption3 fi g L L := by sorry

end PrefixVR
