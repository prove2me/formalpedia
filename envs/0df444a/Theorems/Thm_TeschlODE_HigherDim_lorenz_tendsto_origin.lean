-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_lorenz_tendsto_origin
-- name    : TeschlODE.HigherDim.lorenz_tendsto_origin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T16:48:16.252766+00:00
-- url     : https://prove2.me/theorems/b6a2e939-1ef3-490f-aa08-02f0e965aba3
-- title:
--   Lemma 8.7 — Lorenz equation with $r \le 1$ — the origin is the only fixed point and attracts every solution
-- statement:
--   Consider the Lorenz equation (8.13), $\dot x = -\sigma(x - y)$, $\dot y = r x - y - x z$, $\dot z = x y - b z$, with $\sigma, r, b > 0$, and suppose $r \le 1$. Then
--
--   1. the origin is the only fixed point: $f(v) = 0 \iff v = 0$ for the Lorenz vector field $f$;
--   2. all solutions converge to the origin as $t \to \infty$: for the flow $\Phi$ of (8.13) on $\mathbb{R}^3$ and every $v \in \mathbb{R}^3$, the solution through $v$ exists for all $t \ge 0$ and
--   $$\lim_{t \to \infty} \Phi(t, v) = 0 .$$
--
--   For $r > 1$ two further fixed points appear and the dynamics becomes the famous strange attractor; this lemma is the simple regime.
--
--   **Formalization Note.** $\sigma, r, b > 0$ is the standing assumption of §8.2 and appears as binders. "All solutions converge as $t \to \infty$" includes that they exist for all $t \ge 0$; this is stated explicitly ($[0, \infty) \subseteq I_v$). The flow is quantified universally: any pair $(I, \Phi)$ that is the maximal flow of (8.13) on $\mathbb{R}^3$ (it exists and is unique since the field is polynomial). The second paragraph after the lemma on the page ($r > 1$) is not part of it.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 235, Lemma 8.7

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_lorenzField

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.7, p. 235: for the Lorenz equation (8.13) with `σ, r, b > 0` and `r ≤ 1`,
the origin is the only fixed point, and every solution exists for all `t ≥ 0` and converges to
the origin as `t → ∞`. -/
theorem lorenz_tendsto_origin (σ r b : ℝ) (hσ : 0 < σ) (hr : 0 < r) (hb : 0 < b)
    (hr1 : r ≤ 1) :
    (∀ v : EuclideanSpace ℝ (Fin 3), lorenzField σ r b v = 0 ↔ v = 0) ∧
      ∀ (I : EuclideanSpace ℝ (Fin 3) → Set ℝ)
        (Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
        IsMaximalFlow (lorenzField σ r b) Set.univ I Φ →
          ∀ x : EuclideanSpace ℝ (Fin 3), Set.Ici (0 : ℝ) ⊆ I x ∧
            Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds 0) := by sorry

end TeschlODE.HigherDim
