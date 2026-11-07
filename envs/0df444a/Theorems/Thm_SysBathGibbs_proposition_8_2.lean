-- Prove2me | Theorems.Thm_SysBathGibbs_proposition_8_2
-- name    : SysBathGibbs.proposition_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:37.134203+00:00
-- url     : https://prove2.me/theorems/7438dd55-a186-47c0-9f46-228f5de94608
-- title:
--   Proposition 8.2 — Global gap and comparison for $\mathcal E_{\mathrm{KMS}}$
-- statement:
--   For $\sigma=\beta/2$ there are $C_\Gamma,\lambda>0$, depending only on $\beta$ and $q$, such that for every chain (1.2) on $n\ge1$ sites and every operator $O$,
--   $$
--   \mathcal E_{\mathrm{KMS}}(O)\ge C_\Gamma\sum_{x,a}\|[P_{x,a},O]\|^2_{\rho_\beta}\ge\lambda\|O-\operatorname{Tr}(\rho_\beta O)\mathbf 1\|^2_{\rho_\beta}.
--   $$
--
--   The first inequality compares the Dirichlet form with the Pauli energy; the second is a gap of $\mathcal L_{\mathrm{KMS}}$ independent of $n$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - generalization: "every observable O" → every complex matrix O; reason: the three quadratic forms split into Hermitian and anti-Hermitian parts without cross terms, so the general case specializes to observables and conversely
--   - encoding: E_KMS(O) ∈ ℝ → the real part of the defining expression; reason: the expression is real by Proposition 3.4
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Proposition 8.2 (eq. (8.4)), p.62

import Definitions.Def_SysBathGibbs_Coefficient
import Definitions.Def_SysBathGibbs_Contraction

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Proposition 8.2 (Global gap and comparison)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.62.
When `σ = β/2`, there are `C_Γ, λ > 0`, independent of `n`, such that every observable `O` satisfies
`E_KMS(O) ≥ C_Γ ∑_{x,a} ‖[P_{x,a}, O]‖²_{ρ_β} ≥ λ ‖O - Tr(ρ_β O) 1‖²_{ρ_β}`.

**Formalization Note.** `O` ranges over all complex matrices: §8 applies (8.4) through (8.7) to the
image of every traceless matrix. The constants depend on `β, q` and not on the chain. -/
theorem proposition_8_2 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ CΓ lam : ℝ, 0 < CΓ ∧ 0 < lam ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ O : SysMat n q,
            CΓ * pauliEnergy β (chainHam h) O ≤ kmsDirichlet β h O ∧
            lam * kmsNorm β (chainHam h)
                (O - Matrix.trace (gibbs β (chainHam h) * O) • (1 : SysMat n q)) ^ 2 ≤
              CΓ * pauliEnergy β (chainHam h) O := by sorry

end SysBathGibbs
