-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_final_l1_bound
-- name    : RobustMultitask.Estimator.final_l1_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:50.573358+00:00
-- url     : https://prove2.me/theorems/9c81b1ad-8874-4afe-819c-83cee0c2a6e9
-- title:
--   Proof of Proposition 5, p. 43 — on ℋʲ: ‖β̂ʲ_RM − βʲ‖₁ ≤ 6sλⱼ/(ζψ) + 4‖(β̂†_RM − β†)_{ℐ_poor}‖₁
-- statement:
--   Let $\beta^1,\dots,\beta^N,\beta^\dagger\in\mathbb R^d$ satisfy $\|\beta^k-\beta^\dagger\|_0\le s$ for every task $k$, and fix a task $j$, a level $0<\zeta<1/2$ and $\lambda_j>0$. Let $X\in\mathbb R^{m\times d}$, $m\ge1$, be the design of task $j$ with $\lambda_{\min}(X^\top X/m)\ge\psi>0$, and let $Y=X\beta^j+e$ with a noise vector $e$ in the event $\mathcal H^j$ of (15), $\frac2m\|X^\top e\|_\infty\le\frac{\lambda_j}{2}$. Let $b\in\mathbb R^d$ be any centre (in Algorithm 1, $b=\widehat\beta^\dagger_{\mathrm{RM}}$) and $\widehat\beta$ a global minimizer of $\beta\mapsto\frac1m\|X\beta-Y\|_2^2+\lambda_j\|\beta-b\|_1$. Then
--   $$\frac{1}{2m}\|X(\widehat\beta-\beta^j)\|_2^2+\frac{\lambda_j}{2}\|\widehat\beta-\beta^j\|_1\ \le\ \frac{2(1/\zeta+1)s\lambda_j^2}{\psi}+2\lambda_j\big\|(b-\beta^\dagger)_{\mathcal I_{\mathrm{poor}}}\big\|_1$$
--   and
--   $$\|\widehat\beta-\beta^j\|_1\ \le\ \frac{6s\lambda_j}{\zeta\psi}+4\big\|(b-\beta^\dagger)_{\mathcal I_{\mathrm{poor}}}\big\|_1,$$
--   where $\mathcal I_{\mathrm{poor}}=\mathcal I^\zeta_{\mathrm{poor}}$ (Definition 2).
--
--   These are the two closing inequalities of the proof of Proposition 5; combined with (16) and Lemma 1 they give its high-probability bound. The factor $4$ in front of the shared-estimate error is the source of the coefficient $4C_0$ in the goal theorem.
--
--   **Formalization Note** Deterministic, pointwise on $\mathcal H^j$. Both displayed inequalities are stated (as a conjunction). The centre $b$ is arbitrary; the paper's display is the case $b=\widehat\beta^\dagger_{\mathrm{RM}}$, $m=n_j$, $e=\epsilon^j$. Assumption 1 is needed only for task $j$ and is written in Rayleigh-quotient form.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 43, proof of Proposition 5 (final two displays)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment

namespace RobustMultitask.Estimator

open Matrix

/-- Final display of the proof of Proposition 5, p. 43, on the event `ℋʲ` of (15). Let
`‖βᵏ − β†‖₀ ≤ s` for every task `k`, let `X ∈ ℝ^{m×d}` (`m ≥ 1`) be the design of task `j` with
`λ_min(XᵀX/m) ≥ ψ > 0`, `Y = Xβʲ + e` with `(2/m)‖Xᵀe‖_∞ ≤ λ_j/2`, `λ_j > 0`, `0 < ζ < 1/2`, and
let `β̂` minimize `(1/m)‖Xβ − Y‖₂² + λ_j‖β − b‖₁` (in Algorithm 1, `b = β̂†_RM`). Then
`(1/(2m))‖X(β̂ − βʲ)‖₂² + (λ_j/2)‖β̂ − βʲ‖₁ ≤ 2(1/ζ + 1)sλ_j²/ψ + 2λ_j‖(b − β†)_{ℐ_poor}‖₁`
and `‖β̂ − βʲ‖₁ ≤ 6sλ_j/(ζψ) + 4‖(b − β†)_{ℐ_poor}‖₁`, with `ℐ_poor = ℐ^ζ_poor`. -/
theorem final_l1_bound {N d m : ℕ} (X : Matrix (Fin m) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (ζ ψ : ℝ) (j : Fin N) (lam : ℝ)
    (e : Fin m → ℝ) (b βhat : Fin d → ℝ) (hm : 0 < m)
    (hsparse : ∀ k, l0 (β k - βdag) ≤ s)
    (hψ : 0 < ψ) (hSigma : MinEigAtLeast (sampleCov X) ψ)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hlam : 0 < lam)
    (hH : (2 / (m : ℝ)) * linf (Xᵀ *ᵥ e) ≤ lam / 2)
    (hmin : IsLassoMinimizer X (X *ᵥ β j + e) lam b βhat) :
    (1 / (2 * (m : ℝ))) * l2sq (X *ᵥ (βhat - β j)) + lam / 2 * l1 (βhat - β j)
        ≤ 2 * (1 / ζ + 1) * s * lam ^ 2 / ψ
          + 2 * lam * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag))
      ∧ l1 (βhat - β j)
        ≤ 6 * s * lam / (ζ * ψ) + 4 * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag)) := by sorry

end RobustMultitask.Estimator
