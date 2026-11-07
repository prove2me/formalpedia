-- Prove2me | Theorems.Thm_SysBathGibbs_eq_9_9
-- name    : SysBathGibbs.eq_9_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:15.82085+00:00
-- url     : https://prove2.me/theorems/8caac92e-4f77-4720-89a4-cce87d8ecc36
-- title:
--   Proof of Corollary 9.2, eq. (9.9) — enhanced dissipation of the averaged Dirichlet form
-- statement:
--   There are $n_0\in\mathbb N$ and $c_1>0$, depending only on $\beta$ and $q$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge\max(n_0,1)$ sites, every $T_0>0$ and every state $\rho$,
--   $$
--   \mathcal E_\mu(\rho-\rho_\beta)\ge\frac{c_1}{\log^3(en)}\big(1+\|\Gamma^{-1}(\rho-\rho_\beta)\|^2_{\rho_\beta}\big)\log\big(1+\|\Gamma^{-1}(\rho-\rho_\beta)\|^2_{\rho_\beta}\big),
--   $$
--   where $\mathcal E_\mu$ is the averaged Dirichlet form (8.6) for $T\sim\mu_{T_0}$.
--
--   This logarithmic Sobolev-type gain over the gap estimate is what improves the round count to $\tilde O(n/\varepsilon)$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - reading: "for sufficiently large n, with the threshold depending only on the fixed local parameters"; c1 a constant → ∃ n0 and c1 > 0 depending on β, q only, before the chain and T0; reason: the page's dependence; the estimate is applied pointwise in T and averaged, so it holds for every law μ_{T0}, T0 > 0
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Proof of Corollary 9.2, eq. (9.9), p.74

import Definitions.Def_SysBathGibbs_Contraction
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Proof of Corollary 9.2, eq. (9.9)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.74.
For any state `ρ`, for sufficiently large `n`, with the threshold depending only on the fixed local
parameters, `E_μ(ρ - ρ_β) ≥ (c₁/log³(en)) (1 + ‖Γ⁻¹(ρ - ρ_β)‖²) log(1 + ‖Γ⁻¹(ρ - ρ_β)‖²)`.

**Formalization Note.** `T₀ > 0` is the parameter of the law `μ_{T₀}`, (7.1). `c₁` and the threshold `n₀`
depend on `β, q` only, not on the chain or `T₀`, which is the reading of p.74. -/
theorem eq_9_9 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ (n₀ : ℕ) (c₁ : ℝ), 0 < c₁ ∧
        ∀ (n : ℕ), n₀ ≤ n → 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ T₀ : ℝ, 0 < T₀ → ∀ ρ : SysMat n q, WildeQIT.IsDensityOperator ρ →
            c₁ / Real.log (Real.exp 1 * n) ^ 3 *
                (1 + kmsNorm β (chainHam h)
                    (Gam β (chainHam h) (-1) (ρ - gibbs β (chainHam h))) ^ 2) *
                Real.log (1 + kmsNorm β (chainHam h)
                    (Gam β (chainHam h) (-1) (ρ - gibbs β (chainHam h))) ^ 2) ≤
              Emu β h T₀ (ρ - gibbs β (chainHam h)) := by sorry

end SysBathGibbs
