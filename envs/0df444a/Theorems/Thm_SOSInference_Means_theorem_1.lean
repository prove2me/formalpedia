-- Prove2me | Theorems.Thm_SOSInference_Means_theorem_1
-- name    : SOSInference.Means.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:49.027985+00:00
-- url     : https://prove2.me/theorems/b0b519f6-a7d0-43be-b630-7bfe10ac6846
-- title:
--   Theorem 1 — the rescaled SOS profile function for means converges in distribution to an explicit dimension-dependent limit
-- statement:
--   Assume A1)–A4) in dimension $l$ (in particular $\mathrm{Var}(X)$ exists), let $\theta_*=\mathbb E X_1$, let $R_n^W(\theta_*)$ be the SOS profile function of the sample with $m=\lfloor\kappa n\rfloor$ scenarios, and let $\tilde Z\sim N(0,\mathrm{Var}(X))$ in $\mathbb R^l$. Then, as $n\to\infty$:
--
--   1. if $l=1$: $\ n\,R_n^W(\theta_*)\Rightarrow\sigma^2\chi^2_1$, where $\sigma^2=\mathrm{Var}(X)$ — that is, the law of $\|\tilde Z\|_2^2$;
--   2. if $l=2$:
--   $$n\,R_n^W(\theta_*)\Rightarrow\rho(\tilde Z)\Big(2-\tilde\eta\big(\rho(\tilde Z)\tilde Z\big)\rho(\tilde Z)\Big)\|\tilde Z\|_2^2,$$
--   where $\rho=\rho(\tilde Z)$ is the unique solution of $1/\rho=\tilde g(\rho\tilde Z)$, $\tilde g(x)=\mathbb P(\tau(0)\le\|x\|_2^2)$, $\tilde\eta(x)=\mathbb E[\max(1-\tau(0)/\|x\|_2^2,0)]$, and $\tau$ satisfies $\mathbb P(\tau>t)=\mathbb E[\exp(-(f_X(X_1)+\kappa f_Y(X_1))\pi t)]$;
--   3. if $l\ge3$:
--   $$n^{1/2+3/(2l+2)}\,R_n^W(\theta_*)\Rightarrow\frac{2l+2}{l+2}\cdot\frac{\|\tilde Z\|_2^{1+1/(l+1)}}{\Big(\mathbb E\Big[\frac{\pi^{l/2}}{\Gamma(l/2+1)}\big(f_X(X_1)+\kappa f_Y(X_1)\big)\Big]\Big)^{1/(l+1)}} .$$
--
--   This is the analogue, for the Wasserstein profile with sample-supported alternatives, of Wilks' theorem for empirical likelihood. Unlike the $\chi^2$ limits of empirical likelihood, the rate and the limit depend on the dimension, because mass can only be moved to sample points, whose distance to a given location is of order $n^{-1/l}$.
--
--   **Formalization Note** Convergence in distribution is weak convergence of the laws of $\mathrm{scale}(n)\cdot R_n^W(\theta_*)$ to the image of $N(0,\mathrm{Var}(X))$ under the limit map $\varphi_1$, $\varphi_2$ or $\varphi_l$; measurability of $R_n^W(\theta_*)$ is part of the claim. **The $l=2$ case uses $\tilde\eta(\rho(\tilde Z)\tilde Z)$; Theorem 1 prints $\tilde\eta(\tilde Z)$.** The paper's own derivation (p. 45) evaluates $\|\zeta\|^2\tilde\eta(\zeta)$ at the maximiser $\zeta=-\rho\tilde Z$, which gives $\tilde\eta(\rho\tilde Z)$, and the two laws differ. $R_n^W(\theta_*)$ is $0$ by convention on the event, of probability tending to zero, that the linear program is infeasible; $\rho(0)=0$ by convention, a null event under the Gaussian limit.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, pp. 15–16, Theorem 1

import Mathlib
import Definitions.Def_SOSInference_Means_tauLaw

namespace SOSInference.Means

open MeasureTheory ProbabilityTheory

/-- **Theorem 1** (SOS Profile Function Analysis for Means), pp. 15–16 (Blanchet, Kang, Sample
Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, pp. 15–16, Theorem 1).
Under Assumptions A1)–A4) (A3) gives that `Var(X)` exists), with `Z̃ ~ N(0, Var(X))` on `ℝ^l`:
* `l = 1`: `n R_n^W(θ*) ⇒ σ²χ²₁`, `σ² = Var(X)`, i.e. the law of `‖Z̃‖₂²`;
* `l = 2`: `n R_n^W(θ*) ⇒ ρ(Z̃)(2 − η̃(ρ(Z̃)Z̃) ρ(Z̃)) ‖Z̃‖₂²`, where `ρ(Z̃)` solves `1/ρ = g̃(ρZ̃)`,
  `g̃(x) = P(τ(0) ≤ ‖x‖₂²)`, `η̃(x) = E[max(1 − τ(0)/‖x‖₂², 0)]` and
  `P(τ > t) = E[exp(−(f_X(X_1) + κ f_Y(X_1)) π t)]`;
* `l ≥ 3`: `n^{1/2+3/(2l+2)} R_n^W(θ*) ⇒ (2l+2)/(l+2) · ‖Z̃‖₂^{1+1/(l+1)} /
  (E[π^{l/2}/Γ(l/2+1) (f_X(X_1) + κ f_Y(X_1))])^{1/(l+1)}`.

The printed `l = 2` limit is `ρ(Z̃)(2 − η̃(Z̃)ρ(Z̃))‖Z̃‖₂²`.

**Formalization Note.**
* Convergence in distribution is `TendstoInDistribution` of the real random variables
  `ω ↦ scale(n) · R_n^W(θ*)(ω)` on `(Ω, P)` to `φ_l(Z̃)` with `Z̃` the identity on `ℝ^l` under the
  multivariate Gaussian `N(0, Var(X))`; `φ₁ = ‖·‖²` (`σ²χ²₁` is the law of `‖Z̃‖²` for `l = 1`).
  Measurability of `R_n` is part of the claim.
* **`l = 2` uses `η̃(ρ(Z̃)Z̃)`, not the printed `η̃(Z̃)`**: the derivation on p. 45 evaluates
  `G(ζ*_n, n) = ‖ζ*_n‖² η̃(ζ*_n) + o(1)` at `ζ*_n = −ρ Z_n`, which gives `η̃(ρZ̃)`; the two laws
  differ for every `Z̃ ≠ 0`.
* `R_n^W` is `0` by convention on the (asymptotically negligible) event that the LP is infeasible.
* `m = ⌊κn⌋`; `ρ(0) := 0` (a null event under the Gaussian limit); the samples are indexed
  families. -/
theorem theorem_1 {l : ℕ} (M : Model l) (hM : M.Standing) :
    (l = 1 → TendstoInDistribution (fun n : ℕ => fun ω => (n : ℝ) * Rn M n ω) Filter.atTop
      (fun z : E l => phi1 z) (fun _ => M.P) (multivariateGaussian 0 (covX M))) ∧
    (l = 2 → TendstoInDistribution (fun n : ℕ => fun ω => (n : ℝ) * Rn M n ω) Filter.atTop
      (phi2 M) (fun _ => M.P) (multivariateGaussian 0 (covX M))) ∧
    (3 ≤ l → TendstoInDistribution
      (fun n : ℕ => fun ω => (n : ℝ) ^ ((1 : ℝ) / 2 + 3 / (2 * (l : ℝ) + 2)) * Rn M n ω)
      Filter.atTop (phi3 M) (fun _ => M.P) (multivariateGaussian 0 (covX M))) := by sorry

end SOSInference.Means
