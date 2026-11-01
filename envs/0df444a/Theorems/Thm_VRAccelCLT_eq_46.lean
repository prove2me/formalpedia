-- Prove2me | Theorems.Thm_VRAccelCLT_eq_46
-- name    : VRAccelCLT.eq_46
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:08.212916+00:00
-- url     : https://prove2.me/theorems/c6550583-5c09-4618-b505-de96c87c71bd
-- title:
--   Display (46): $\rho(H_2)=\max_i\sqrt{\beta(1-\alpha\lambda_i)}\le 1-\gamma<\rho_2<\rho_2^{1/2}$
-- statement:
--   Let $H\in\mathbb R^{m\times m}$ be symmetric with eigenvalues $\lambda_i\in[\eta,L]$, where $0<\eta\le L$. Let $\alpha\in(0,1/L]$, $\gamma=\sqrt{\alpha\eta}$, $\beta=\frac{1-\gamma}{1+\gamma}$ and $\rho_2\in(1-\gamma,1)$, and let
--
--   $$
--   H_2=\begin{pmatrix}(1+\beta)(I_m-\alpha H) & -\beta(I_m-\alpha H)\\ I_m & 0_m\end{pmatrix}.
--   $$
--
--   Then
--
--   $$
--   \rho(H_2)=\max_i\sqrt{\beta(1-\alpha\lambda_i)}\ \le\ \sqrt{\beta(1-\alpha\eta)}=\sqrt{\frac{(1-\gamma)(1-\gamma^2)}{1+\gamma}}=1-\gamma<\rho_2<\rho_2^{1/2}. \tag{46}
--   $$
--
--   Every link of the chain is asserted. Consequently $\rho(P_2)=\rho_2^{-1/2}\rho(H_2)<1$, the stability statement of Theorem 2.
--
--   **Formalization Note** $\rho$ is the complex spectral radius with values in $[0,\infty]$; the maximum over $i$ is a supremum in $[0,\infty]$ of the nonnegative reals $\sqrt{\beta(1-\alpha\lambda_i)}$, which is the maximum for $m\ge1$ (and $0=\rho(H_2)$ for $m=0$).
--
--   Differences from the source:
--   - encoding: standing assumptions where (46) is derived (Assumption 1, α ∈ (0, 1/L], H the symmetric Hessian with λ_i ∈ [η, L]) → explicit hypotheses 0 < η ≤ L, 0 < L, 0 < α ≤ 1/L, H symmetric with eigenvalues in [η, L]; reason: the sentence of (46) names γ, β, ρ2 and λ_i ∈ [η, L]; the rest are the hypotheses of Theorem 2 in force on p.20
--   - encoding: γ² = αη → γ = √(αη); reason: γ ≜ √(αη) in Theorem 2; same value
--   - encoding: max_i over i = 1, …, m → supremum in [0, ∞] of ofReal √(β(1 − αλ_i)); reason: equal to the maximum for m ≥ 1; the spectral radius lives in [0, ∞]
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, display (46), proof of Theorem 2, p.20

import Mathlib
import Definitions.Def_VRAccelCLT_specRad
import Definitions.Def_VRAccelCLT_accelBlock

namespace VRAccelCLT

/-- **Display (46): the spectral radius of `H₂`.** Lei, Shanbhag, arXiv:2006.07769v3, proof of
Theorem 2, p.20: "Since γ2 = αη, β = (1−γ)/(1+γ), ρ2 ∈ (1 − γ, 1), and λi ∈ [η, L], we obtain that
ρ(H2) = max_i √(β(1 − αλi)) ≤ √(β(1 − αη)) = √((1−γ)(1−γ2)/(1+γ)) = 1 − γ < ρ2 < ρ2^{1/2}. (46)"

For a symmetric `H` with eigenvalues `λ_i ∈ [η, L]`, `0 < η ≤ L`, `α ∈ (0, 1/L]`, `γ = √(αη)`,
`β = (1−γ)/(1+γ)` and `ρ₂ ∈ (1 − γ, 1)`, every link of the chain (46) holds, with
`H₂ = accelBlock α β H`.

**Formalization Note.** `ρ(H₂)` is `specRad` (complex spectrum, value in `ℝ≥0∞`); the maximum over
`i` is the supremum in `ℝ≥0∞` of `ofReal √(β(1 − αλ_i))` (a maximum for `m ≥ 1`, and `0 = ρ(H₂)` for
`m = 0`). `0 < η ≤ L` and `L > 0` are the standing Assumption 1 constants of the proof. -/
theorem eq_46 {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.IsHermitian)
    (η L α γ β ρ₂ : ℝ) (hη : 0 < η) (hL : 0 < L) (hηL : η ≤ L)
    (hlam : ∀ i, η ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ L)
    (hα : 0 < α) (hαL : α ≤ 1 / L) (hγ : γ = Real.sqrt (α * η)) (hβ : β = (1 - γ) / (1 + γ))
    (hρ : 1 - γ < ρ₂) (hρ1 : ρ₂ < 1) :
    specRad (accelBlock α β H) =
        ⨆ i, ENNReal.ofReal (Real.sqrt (β * (1 - α * hH.eigenvalues i))) ∧
      (⨆ i, ENNReal.ofReal (Real.sqrt (β * (1 - α * hH.eigenvalues i))))
        ≤ ENNReal.ofReal (Real.sqrt (β * (1 - α * η))) ∧
      Real.sqrt (β * (1 - α * η)) = Real.sqrt ((1 - γ) * (1 - γ ^ 2) / (1 + γ)) ∧
      Real.sqrt ((1 - γ) * (1 - γ ^ 2) / (1 + γ)) = 1 - γ ∧
      1 - γ < ρ₂ ∧ ρ₂ < ρ₂ ^ (1 / 2 : ℝ) := by sorry

end VRAccelCLT
