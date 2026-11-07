-- Prove2me | Theorems.Thm_SysBathGibbs_theorem_7_1
-- name    : SysBathGibbs.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:37.793571+00:00
-- url     : https://prove2.me/theorems/6526fe37-6f9b-493a-8fae-449e714a6bc3
-- title:
--   Theorem 7.1 — Approximate stationary state $\rho_*$
-- statement:
--   There are $c_0,C>0$, depending only on $\beta$ and $q$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge1$ sites and all real $\alpha$, $T_0$ with
--   $$
--   0<\alpha^2\sigma<1,\qquad n\alpha^2\sigma\le c_0,\qquad T_0\ge\max\Big\{1,2\sigma\sqrt{2\log\tfrac1{\alpha^2\sigma}}\Big\},
--   $$
--   the matrix $\rho_*=\rho_\beta+\alpha^2\Gamma(X)$ of (7.8) is a state and
--   $$
--   \rho_*\succeq\rho_\beta/2,\qquad \|\Gamma^{-1}(\rho_*-\rho_\beta)\|_{\rho_\beta}\le\frac{C\alpha^2\sqrt n}{T_0},\qquad \|\Gamma^{-1}(\Phi^{\mu_{T_0}}_\alpha(\rho_*)-\rho_*)\|_{\rho_\beta}\le Cn\alpha^4,
--   $$
--   and the same upper bounds hold for $\|\rho_*-\rho_\beta\|_1$ and $\|\Phi^{\mu_{T_0}}_\alpha(\rho_*)-\rho_*\|_1$.
--
--   The stationarity defect $Cn\alpha^4$ of $\rho_*$ is what makes the final bias $O(n\alpha^2)$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - reading: "for sufficiently small c0 > 0" → ∃ c0 > 0 (with C); reason: the hypotheses (7.9) only strengthen as c0 decreases, so one c0 covers every smaller value with the same C
--   - encoding: ρ∗ built from H_Lamb → ρ∗ built from the Gibbs-centered B^Lamb_x; reason: the paper prescribes the centering before (7.4), p.55
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Theorem 7.1 (eqs. (7.9)–(7.10)), p.56

import Definitions.Def_SysBathGibbs_Stationary
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix MeasureTheory
open scoped ComplexOrder

namespace SysBathGibbs

/-- **Theorem 7.1 (Approximate stationary state)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.56.
For sufficiently small `c₀ > 0`, suppose (7.9): `0 < α²σ < 1`, `nα²σ ≤ c₀`,
`T₀ ≥ max{1, 2σ√(2 log(1/(α²σ)))}`. Then `ρ∗` of (7.8) is a state, `ρ∗ ⪰ ρ_β/2`,
`‖Γ⁻¹(ρ∗ - ρ_β)‖ ≤ Cα²√n/T₀`, `‖Γ⁻¹(Φ^{μ_{T₀}}_α(ρ∗) - ρ∗)‖ ≤ Cnα⁴`. The same upper bounds hold in
trace norm for the two differences.

**Formalization Note.** Here `ρ∗` uses the Gibbs-centered `B^Lamb_x`, p.55. The hypotheses (7.9) become
stronger as `c₀` decreases, so one `c₀` covers all smaller values. -/
theorem theorem_7_1 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ α T₀ : ℝ, 0 < α ^ 2 * (β / 2) → α ^ 2 * (β / 2) < 1 → n * α ^ 2 * (β / 2) ≤ c₀ →
            T0Choice β α ≤ T₀ →
            WildeQIT.IsDensityOperator (rhoStar β h α T₀) ∧
            (rhoStar β h α T₀ - (1 / 2 : ℂ) • gibbs β (chainHam h)).PosSemidef ∧
            kmsNorm β (chainHam h)
                (Gam β (chainHam h) (-1) (rhoStar β h α T₀ - gibbs β (chainHam h))) ≤
              C * α ^ 2 * Real.sqrt n / T₀ ∧
            kmsNorm β (chainHam h)
                (Gam β (chainHam h) (-1) (Phi β h α T₀ (rhoStar β h α T₀) - rhoStar β h α T₀)) ≤
              C * n * α ^ 4 ∧
            WildeQIT.traceNorm (rhoStar β h α T₀ - gibbs β (chainHam h)) ≤
              C * α ^ 2 * Real.sqrt n / T₀ ∧
            WildeQIT.traceNorm (Phi β h α T₀ (rhoStar β h α T₀) - rhoStar β h α T₀) ≤
              C * n * α ^ 4 := by sorry

end SysBathGibbs
