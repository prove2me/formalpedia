-- Prove2me | Theorems.Thm_TrustIPM_theorem_1
-- name    : TrustIPM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:40.971959+00:00
-- url     : https://prove2.me/theorems/a6406de7-1341-44b7-96dc-affec888f1ae
-- title:
--   Theorem 1 — Trust-IPM finds an approximate second-order SIP in $O\bigl(1+\frac{\psi_\mu(x^{(0)})-\psi^*_\mu}{\mu}(\frac{L_1}{\mu\tau_l^2})^{3/4}\bigr)$ iterations (corrected: (SIP2) sign)
-- statement:
--   Suppose Assumptions 1, 2 and 3 hold, with $\tau_l>0$ and $\tau_c=(\tau_l^2\mu/L_1)^{1/2}$, and run Trust-IPM$(f,a,\mu,\tau_l,L_1,\eta,x^{(0)})$ with
--
--   $$
--   \eta=\frac1{50}\Bigl(\frac{\tau_l^2\mu}{L_1}\Bigr)^{1/4}.\tag{35}
--   $$
--
--   Then the algorithm terminates within
--
--   $$
--   O\Bigl(1+\frac{\psi_\mu(x^{(0)})-\psi^*_\mu}{\mu}\Bigl(\frac{L_1}{\mu\tau_l^2}\Bigr)^{3/4}\Bigr)
--   $$
--
--   iterations with a $(\mu,\tau_l,\tau_c)$-approximate second-order SIP $(x^+,y^+)$, i.e. (SIP1) and (SIP2) hold, where (SIP2) reads
--
--   $$
--   \nabla^2_{xx}\mathcal L(x^+,y^+)+\mu\nabla a(x^+)^T(S^+)^{-2}\nabla a(x^+)\succeq-\tau_c^{1/2}L_1(1+\|y^+\|_1)I .
--   $$
--
--   Precisely: there is an absolute constant $C$ such that for all dimensions $n,m\ge1$ and all data satisfying the assumptions, a run of Trust-IPM exists, and every run (whatever minimizer each Take-step picks) reaches, at some loop index $k$ with $k+1\le C\bigl(1+\frac{\psi_\mu(x^{(0)})-\psi^*_\mu}{\mu}(\frac{L_1}{\mu\tau_l^2})^{3/4}\bigr)$, a pair $(x_{k+1},y_k)$ satisfying (SIP1) and (SIP2). Since $\mu$ and $\tau_l^2\mu$ scale together, for fixed $\tau_l$ this is an $O(\mu^{-7/4})$ bound for finding an approximate Fritz John point of a problem with nonconvex constraints.
--
--   **Formalization Note** The constant $C$ is quantified before the dimensions, the functions and every parameter. The run relation and the iteration count are as in the Algorithm 1 module: the algorithm returns at the first loop index $k$ where $(x_{k+1},y_k)$ passes the test, after $k+1$ calls of Take-step.
--
--   Differences from the source:
--   - correction: (SIP2) with right-hand side +τ_c^{1/2}L₁(1 + ‖y‖₁)I (Definition 3, p.7) → −τ_c^{1/2}L₁(1 + ‖y‖₁)I; reason: printed + sign: n=m=1, f≡0, a(x)=1−x², L₁=2, L₂=1, µ=1/2, τ_l=1, x⁰=0 satisfy Assumptions 1–3, every iterate is x=0, y⁺=1/2, (SIP1) holds and the printed (SIP2) needs 1 ≥ 2^{-1/2}·2·3/2, false, so Trust-IPM never terminates
--   - encoding: takes at most O(1 + (ψµ(x⁰) − ψ*µ)/µ · (L₁/(µτ_l²))^{3/4}) iterations → ∃ C absolute, every run has k with k + 1 ≤ C·(…) and (SIP1), (SIP2) at (xs (k+1), ys k); reason: the algorithm returns at the first such k after k + 1 iterations; O(·) has a constant independent of all data
--   - reading: Trust-IPM(f, a, µ, τ_l, L₁, η, x⁽⁰⁾) can be run → the conclusion also states that a run exists; reason: the page presupposes the algorithm is well defined; stating it keeps the 'every run' clause from being vacuous
--   - reading: τ_l (Definition 2, Assumption 3) → hypothesis 0 < τ_l; reason: the paper fixes τ_l ∈ (0, ∞) on p.7; Assumption 3 alone allows τ_l < 0, for which (SIP1.c) cannot hold
--   - encoding: (x⁺, y⁺) ← Take-step(f, a, µ, x, η) → IsTakeStep for every argmin selection d_x, with α = 1 when S⁻¹d_s = 0; reason: Take-step chooses any element of the argmin; η/0 = +∞ on the page
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Theorem 1, p.19 (proof pp.19–20; (SIP2) sign from Lemma 11's proof, p.19)

import Mathlib
import Definitions.Def_TrustIPM_IsTakeStep

namespace TrustIPM

/-- **Theorem 1** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Theorem 1, p.19), with (SIP2) sign corrected. Suppose
Assumptions 1, 2 and 3 hold. Then `Trust-IPM(f, a, µ, τ_l, L₁, η, x⁽⁰⁾)` with
`η = (1/50)(τ_l²µ/L₁)^{1/4}` (35) takes at most
`O(1 + (ψµ(x⁽⁰⁾) − ψ*µ)/µ · (L₁/(µτ_l²))^{3/4})` iterations to terminate with a
`(µ, τ_l, τ_c)`-approximate second-order SIP `(x⁺, y⁺)`, i.e. (SIP1) and (SIP2) hold.

**Formalization Note** The `O(·)` constant `C` is absolute: it is chosen before the dimensions, the
functions and all parameters. A run of Trust-IPM is any sequence produced by Take-step with any argmin
selection (`IsRun`); the statement asserts that a run exists and that every run reaches, at some loop
index `k` with `k + 1 ≤ C·(…)` (i.e. within that many iterations), a pair `(xs (k+1), ys k)` satisfying
(SIP1) and (SIP2), so the algorithm returns there or earlier. `τ_c = (τ_l²µ/L₁)^{1/2}` is fixed by
Assumption 3 and (SIP2) carries the corrected sign `−τ_c^{1/2}L₁(1 + ‖y‖₁)I`. `τ_l ∈ (0, ∞)` (p.7) and
`n, m` are positive integers (p.1). -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ (n m : ℕ), 0 < n → 0 < m →
      ∀ (f : E n → ℝ) (a : Fin m → E n → ℝ) (L₁ L₂ μ τl : ℝ) (x₀ : E n),
        Assumption1 f a L₁ L₂ → Assumption2 f a μ x₀ → Assumption3 L₁ L₂ μ τl → 0 < τl →
        (∃ (xs ds : ℕ → E n) (ys : ℕ → Fin m → ℝ),
            IsRun f a μ L₁ (1 / 50 * (τl ^ 2 * μ / L₁) ^ ((1 : ℝ) / 4)) x₀ xs ds ys) ∧
        ∀ (xs ds : ℕ → E n) (ys : ℕ → Fin m → ℝ),
          IsRun f a μ L₁ (1 / 50 * (τl ^ 2 * μ / L₁) ^ ((1 : ℝ) / 4)) x₀ xs ds ys →
          ∃ k : ℕ,
            (k : ℝ) + 1 ≤ C * (1 + (barrier f a μ x₀ - barrierInf f a μ) / μ *
              (L₁ / (μ * τl ^ 2)) ^ ((3 : ℝ) / 4)) ∧
            SIP1 f a μ τl (tauC L₁ μ τl) (xs (k + 1)) (ys k) ∧
            SIP2 f a μ (tauC L₁ μ τl) L₁ (xs (k + 1)) (ys k) := by sorry

end TrustIPM
