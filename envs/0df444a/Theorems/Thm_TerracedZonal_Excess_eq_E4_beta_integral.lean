-- Prove2me | Theorems.Thm_TerracedZonal_Excess_eq_E4_beta_integral
-- name    : TerracedZonal.Excess.eq_E4_beta_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:18.40486+00:00
-- url     : https://prove2.me/theorems/0dceae36-9d87-4a3e-82de-012ddfcced14
-- title:
--   App. E.4 — the Beta integral $\int_0^\pi(\cos^2\theta\sin\theta)^{1/3}d\theta=B(\tfrac23,\tfrac56)$ and $\int f_\lambda\,dk=C(\lambda)N^{2/3}$
-- statement:
--   The integral of the per-ring minimum cost over the sphere:
--
--   1. $$\int_0^\pi\big(\cos^2\theta\sin\theta\big)^{1/3}\,d\theta=B\big(\tfrac23,\tfrac56\big)=\frac{\Gamma(2/3)\Gamma(5/6)}{\Gamma(3/2)};$$
--   2. for every $\lambda>0$ and every $N\ge1$, on $0<\theta<\pi$ the minimum per-ring cost satisfies $f_\lambda(\theta)=3\big(A(\theta)B_\lambda(\theta)^2/4\big)^{1/3}$, and
--
--   $$\int_0^\pi f_\lambda(\theta)\,\frac{N^{1/2}}{C_0}\,d\theta=C(\lambda)\,N^{2/3},$$
--
--   with $A$, $B_\lambda$ of (31)–(32), $f_\lambda$ the closed form after (33) and $C(\lambda)$ of (29). Since one ring occupies $d\theta=C_0N^{-1/2}$ of colatitude, the left side is the continuum total cost $\int f_\lambda\,dk$ appearing in Lemma E.5.
--
--   Differences from the source:
--   - encoding: f_λ(θ) = 3(A(θ)B_λ(θ)²/4)^{1/3} = 3(c_stretch λ²C₀⁵/384 · cos²θ sin θ)^{1/3} N^{1/6} → f_λ is defined by the second (closed) form and the equality with the first form is a conjunct, asserted for θ ∈ (0, π); reason: A(θ) has sin θ in its denominator, so the first form is meaningful only on (0, π); the conjunct keeps the paper equality as a claim instead of a definition
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), App. E.4, display after (33), p. 29 (PDF 30)

import Definitions.Def_TerracedZonal_Excess_ContinuumCosts

namespace TerracedZonal.Excess

open Real

/-- App. E.4, display after (33), p. 29 (PDF 30):
`∫₀^π (cos²θ sin θ)^{1/3} dθ = B(2/3, 5/6)`; for every `λ > 0` and `N ≥ 1`,
`f_λ(θ) = 3 (A(θ) B_λ(θ)² / 4)^{1/3}` on `(0, π)` and
`∫₀^π f_λ(θ) (N^{1/2}/C₀) dθ = C(λ) N^{2/3}`. -/
theorem eq_E4_beta_integral :
    (∫ θ in (0 : ℝ)..π, (Real.cos θ ^ 2 * Real.sin θ) ^ (1 / 3 : ℝ)) = betaB ∧
    ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, 0 < N →
      (∀ θ ∈ Set.Ioo (0 : ℝ) π,
        fLam lam N θ = 3 * (Acoef N θ * Bcoef lam N θ ^ 2 / 4) ^ (1 / 3 : ℝ)) ∧
      (∫ θ in (0 : ℝ)..π, fLam lam N θ * ((N : ℝ) ^ (1 / 2 : ℝ) / C0))
        = Cfun lam * (N : ℝ) ^ (2 / 3 : ℝ) := by sorry

end TerracedZonal.Excess
