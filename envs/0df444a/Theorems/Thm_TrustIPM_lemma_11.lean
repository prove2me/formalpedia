-- Prove2me | Theorems.Thm_TrustIPM_lemma_11
-- name    : TrustIPM.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:52.968344+00:00
-- url     : https://prove2.me/theorems/a5a686eb-550d-4796-b1dd-30f041c9291f
-- title:
--   Lemma 11 — small predicted progress at $x$ and $x^+$ gives (SIP1) and (SIP2) (corrected: (SIP2) sign)
-- statement:
--   Suppose Assumptions 1 and 3 hold, $\tau_l>0$, $\tau_c=(\tau_l^2\mu/L_1)^{1/2}$, $x\in\mathcal X$ and
--
--   $$
--   \eta\in\Bigl(0,\frac1{50}\Bigl(\frac{\tau_l^2\mu}{L_1}\Bigr)^{1/4}\Bigr].
--   $$
--
--   Let $(x^+,y^+)$ be an output of Take-step$(f,a,\mu,x,\eta)$ with direction $d_x$, and assume $\mathcal M^{\psi_\mu}_x(d_x)\ge-5\eta^3\mu$. Then
--
--   1. $(x^+,y^+)$ satisfies (SIP1) with $(\mu,\tau_l,\tau_c)$;
--   2. if $d_{x^+}$ is a direction Take-step can compute at $x^+$ (a minimizer of $\mathcal M^{\psi_\mu}_{x^+}$ over the ball of radius $r^+$ of line 16 at $x^+$) and $\mathcal M^{\psi_\mu}_{x^+}(d_{x^+})\ge-5\eta^3\mu$, then $(x^+,y^+)$ satisfies (SIP2) in the form
--   $$\nabla^2_{xx}\mathcal L(x^+,y^+)+\mu\nabla a(x^+)^T(S^+)^{-2}\nabla a(x^+)\succeq-\tau_c^{1/2}L_1(1+\|y^+\|_1)I .$$
--
--   So the algorithm stops as soon as two consecutive iterations have small predicted progress.
--
--   Differences from the source:
--   - correction: (SIP2) with right-hand side +τ_c^{1/2}L₁(1 + ‖y‖₁)I (Definition 3, p.7) → −τ_c^{1/2}L₁(1 + ‖y‖₁)I; reason: printed + sign: n=m=1, f≡0, a(x)=1−x², L₁=2, L₂=1, µ=1/2, τ_l=1, x⁰=0 satisfy Assumptions 1–3, every iterate is x=0, y⁺=1/2, (SIP1) holds and the printed (SIP2) needs 1 ≥ 2^{-1/2}·2·3/2, false, so Trust-IPM never terminates; the proof of Lemma 11 derives the − form
--   - reading: τ_l (Definition 2, Assumption 3) → hypothesis 0 < τ_l; reason: the paper fixes τ_l ∈ (0, ∞) on p.7; Assumption 3 alone allows τ_l < 0, for which (SIP1.c) cannot hold
--   - encoding: (x⁺, y⁺) ← Take-step(f, a, µ, x, η) → IsTakeStep for every argmin selection d_x, with α = 1 when S⁻¹d_s = 0; reason: Take-step chooses any element of the argmin; η/0 = +∞ on the page
--   - encoding: d_{x⁺}, the direction computed by Algorithm 1 at x⁺ → every minimizer of the model at x⁺ over the ball of x⁺'s radius (IsTRDirection); reason: Take-step at x⁺ may choose any element of the argmin
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 11, p.16 (proof pp.16–19; (SIP2) sign from the last display of p.19)

import Mathlib
import Definitions.Def_TrustIPM_IsTakeStep

namespace TrustIPM

/-- **Lemma 11** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 11, p.16), with (SIP2) sign corrected. Let `d_x`
and `d_{x⁺}` be directions computed by Algorithm 1 at the iterate `x` and at `x⁺`. Suppose
Assumptions 1 and 3 hold, `x ∈ X`, `η ∈ (0, (1/50)(τ_l²µ/L₁)^{1/4}]`, and
`M^{ψµ}_x(d_x) ≥ −5η³µ`. Then `(x⁺, y⁺) ← Take-step(f, a, µ, x, η)` satisfies (SIP1). Additionally, if
`M^{ψµ}_{x⁺}(d_{x⁺}) ≥ −5η³µ` then `(x⁺, y⁺)` satisfies (SIP2).

**Formalization Note** (SIP1), (SIP2) are with `(µ, τ_l, τ_c)`, `τ_c = (τ_l²µ/L₁)^{1/2}` fixed by
Assumption 3, and (SIP2) carries the sign `−τ_c^{1/2}L₁(1 + ‖y‖₁)I` that the proof (p.19) derives. The
statement covers every argmin selection `d_x` (inside `IsTakeStep`) and every `d_{x⁺}` in the argmin
of the model at `x⁺` over the ball of `x⁺`'s radius (`IsTRDirection`). `τ_l ∈ (0, ∞)` is the paper's
frame for the tolerance (p.7); `n, m` are positive integers (p.1). -/
theorem lemma_11 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (f : E n → ℝ) (a : Fin m → E n → ℝ)
    (L₁ L₂ μ τl η : ℝ) (x d xp : E n) (yp : Fin m → ℝ) (hA1 : Assumption1 f a L₁ L₂)
    (hA3 : Assumption3 L₁ L₂ μ τl) (hτl : 0 < τl) (hx : x ∈ feasibleSet a) (hη₀ : 0 < η)
    (hη : η ≤ 1 / 50 * (τl ^ 2 * μ / L₁) ^ ((1 : ℝ) / 4))
    (hstep : IsTakeStep f a μ L₁ η x d xp yp) (hM : -5 * η ^ 3 * μ ≤ model f a μ x d) :
    SIP1 f a μ τl (tauC L₁ μ τl) xp yp ∧
      ∀ dp : E n, IsTRDirection f a μ L₁ η xp dp → -5 * η ^ 3 * μ ≤ model f a μ xp dp →
        SIP2 f a μ (tauC L₁ μ τl) L₁ xp yp := by sorry

end TrustIPM
