-- Prove2me | Theorems.Thm_SysBathGibbs_theorem_9_1
-- name    : SysBathGibbs.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:33.015867+00:00
-- url     : https://prove2.me/theorems/fcc0a859-9be1-421a-84b2-a9aa01edb938
-- title:
--   Theorem 9.1 — Physical-channel mixing and stationary-state bias
-- statement:
--   There are $c_0,\kappa,C>0$, depending only on $\beta$ and $q$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge1$ sites and all real $\alpha$, $T_0$ satisfying (7.9) with this $c_0$, the averaged physical channel $\Phi=\Phi^{\mu_{T_0}}_\alpha$ has a unique stationary state $\rho_\infty$, and
--
--   1. $\|\Gamma^{-1}\Phi(\delta)\|_{\rho_\beta}\le(1-\kappa\alpha^2)\|\Gamma^{-1}\delta\|_{\rho_\beta}$ for every $\delta$ with $\operatorname{Tr}\delta=0$;
--   2. $\|\Gamma^{-1}(\rho_\infty-\rho_*)\|_{\rho_\beta}\le Cn\alpha^2$;
--   3. $\|\rho_\infty-\rho_\beta\|_1\le\|\Gamma^{-1}(\rho_\infty-\rho_\beta)\|_{\rho_\beta}\le Cn\alpha^2+C\alpha^2\sqrt n/T_0$;
--   4. for every state $\rho_0$ and $m\ge0$,
--   $$
--   \|\Phi^m(\rho_0)-\rho_\beta\|_1\le e^{-\kappa\alpha^2m}\|\Gamma^{-1}(\rho_0-\rho_\infty)\|_{\rho_\beta}+Cn\alpha^2+C\alpha^2\frac{\sqrt n}{T_0}.
--   $$
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - reading: "(7.9) holds with sufficiently small c0 > 0" → ∃ c0 > 0; reason: the hypotheses only strengthen as c0 decreases
--   - encoding: "a unique stationary state ρ∞" → ∃ a density operator fixed by Φ, equal to every density operator fixed by Φ; reason: the definition of uniqueness among states
--   - encoding: "in the setting of Propositions 8.1 and 8.2" → only the chain (1.2) at σ = β/2; reason: both propositions are consequences of (1.2), not further assumptions
--   - encoding: δ a traceless state difference → δ any traceless complex matrix; reason: the page says ∀δ with Tr δ = 0; Φ acts by the same linear formula
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Theorem 9.1 (eqs. (9.1)–(9.4)), p.72

import Definitions.Def_SysBathGibbs_Stationary
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Theorem 9.1 (Physical-channel mixing and stationary-state bias)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.72.
Suppose (7.9) holds with sufficiently small `c₀ > 0`. The averaged physical channel `Φ` has a unique
stationary state `ρ_∞`. There is `κ > 0`, independent of `n, α, T₀`, such that (9.1)
`‖Γ⁻¹Φ(δ)‖ ≤ (1 - κα²)‖Γ⁻¹δ‖` for `Tr δ = 0`; (9.2) `‖Γ⁻¹(ρ_∞ - ρ∗)‖ ≤ Cnα²`; (9.3)
`‖ρ_∞ - ρ_β‖₁ ≤ ‖Γ⁻¹(ρ_∞ - ρ_β)‖ ≤ Cnα² + Cα²√n/T₀`; and (9.4), for every initial state `ρ₀` and integer
`m ≥ 0`, `‖Φ^m(ρ₀) - ρ_β‖₁ ≤ e^{-κα²m}‖Γ⁻¹(ρ₀ - ρ_∞)‖ + Cnα² + Cα²√n/T₀`.

**Formalization Note.** The theorem's "setting of Propositions 8.1 and 8.2" is only (1.2) at `σ = β/2`:
both propositions are consequences, and they are not hypotheses. `δ` ranges over all traceless
complex matrices, on which `Φ` acts by the same formula. -/
theorem theorem_9_1 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ c₀ κ C : ℝ, 0 < c₀ ∧ 0 < κ ∧ 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ α T₀ : ℝ, 0 < α ^ 2 * (β / 2) → α ^ 2 * (β / 2) < 1 → n * α ^ 2 * (β / 2) ≤ c₀ →
            T0Choice β α ≤ T₀ →
            ∃ ρinf : SysMat n q,
              (WildeQIT.IsDensityOperator ρinf ∧ Phi β h α T₀ ρinf = ρinf ∧
                ∀ ρ' : SysMat n q, WildeQIT.IsDensityOperator ρ' → Phi β h α T₀ ρ' = ρ' →
                  ρ' = ρinf) ∧
              (∀ δ : SysMat n q, Matrix.trace δ = 0 →
                kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (Phi β h α T₀ δ)) ≤
                  (1 - κ * α ^ 2) * kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) δ)) ∧
              kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (ρinf - rhoStar β h α T₀)) ≤
                C * n * α ^ 2 ∧
              WildeQIT.traceNorm (ρinf - gibbs β (chainHam h)) ≤
                kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (ρinf - gibbs β (chainHam h))) ∧
              kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (ρinf - gibbs β (chainHam h))) ≤
                C * n * α ^ 2 + C * α ^ 2 * Real.sqrt n / T₀ ∧
              ∀ (ρ₀ : SysMat n q) (m : ℕ), WildeQIT.IsDensityOperator ρ₀ →
                WildeQIT.traceNorm ((Phi β h α T₀)^[m] ρ₀ - gibbs β (chainHam h)) ≤
                  Real.exp (-(κ * α ^ 2 * m)) *
                      kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (ρ₀ - ρinf)) +
                    C * n * α ^ 2 + C * α ^ 2 * Real.sqrt n / T₀ := by sorry

end SysBathGibbs
