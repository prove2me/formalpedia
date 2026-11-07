-- Prove2me | Theorems.Thm_SysBathGibbs_theorem_8_3
-- name    : SysBathGibbs.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:04.528935+00:00
-- url     : https://prove2.me/theorems/18f2cde5-80da-4bfc-9ba6-629d436e7e7a
-- title:
--   Theorem 8.3 — Contraction of $\Theta_s$
-- statement:
--   There are $\lambda>0$ and $c_*>0$, depending only on $\beta$ and $q$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge1$ sites, all $s$, $T_0$ with $0<ns\le c_*$ and $T_0\ge1$, and every traceless $X$:
--   $\mathcal D_\mu(X)\ge0$ and $\mathcal E_\mu(X)\ge\lambda\|\Gamma^{-1}(X)\|^2_{\rho_\beta}$ (8.7), and
--   $$
--   \|\Gamma^{-1}(\Theta_sX)\|^2_{\rho_\beta}\le\|\Gamma^{-1}(X)\|^2_{\rho_\beta}-\tfrac12\mathcal D_\mu(X)-\tfrac12s\,\mathcal E_\mu(X)\le\big(1-\tfrac12\lambda s\big)\|\Gamma^{-1}(X)\|^2_{\rho_\beta}.
--   $$
--
--   The averaged ideal channel contracts by $1-\Theta(s)$ even though the Lamb shift has extensive norm.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - reading: λ of Proposition 8.2, entering through (8.7) → ∃ λ > 0 with (8.7) E_µ(X) ≥ λ‖Γ⁻¹X‖² and D_µ(X) ≥ 0 as conjuncts; reason: ties λ to the Dirichlet form, as (8.7) does on p.63
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Theorem 8.3 (eq. (8.8)), with (8.7), p.63

import Definitions.Def_SysBathGibbs_Contraction

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Theorem 8.3 (Contraction of `Θ_s`)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.63, with (8.7).
There is `c⋆ > 0`, independent of `n, s, T₀`, such that `0 < ns ≤ c⋆`, `T₀ ≥ 1` imply, for every
traceless `X`, `‖Γ⁻¹(Θ_s X)‖² ≤ ‖Γ⁻¹(X)‖² - ½D_μ(X) - ½sE_μ(X) ≤ (1 - ½λs)‖Γ⁻¹(X)‖²`.

**Formalization Note.** The page's `λ` is that of Proposition 8.2, through (8.7),
`E_μ(X) ≥ λ‖Γ⁻¹(X)‖²` (and `D_μ(X) ≥ 0`). So `λ` is existential here and (8.7) is a conjunct, which ties it to
the Dirichlet form. `X` is any traceless complex matrix. -/
theorem theorem_8_3 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ lam cStar : ℝ, 0 < lam ∧ 0 < cStar ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ T₀ s : ℝ, 0 < n * s → n * s ≤ cStar → 1 ≤ T₀ →
            ∀ X : SysMat n q, Matrix.trace X = 0 →
              0 ≤ Dmu β h T₀ X ∧
              lam * kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) X) ^ 2 ≤ Emu β h T₀ X ∧
              kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (Theta β h T₀ s X)) ^ 2 ≤
                kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) X) ^ 2 -
                  (1 / 2) * Dmu β h T₀ X - (1 / 2) * s * Emu β h T₀ X ∧
              kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) X) ^ 2 -
                  (1 / 2) * Dmu β h T₀ X - (1 / 2) * s * Emu β h T₀ X ≤
                (1 - (1 / 2) * lam * s) *
                  kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) X) ^ 2 := by sorry

end SysBathGibbs
