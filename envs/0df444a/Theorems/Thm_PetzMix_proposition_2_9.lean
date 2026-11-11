-- Prove2me | Theorems.Thm_PetzMix_proposition_2_9
-- name    : PetzMix.proposition_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:40.743789+00:00
-- url     : https://prove2.me/theorems/b7b3997f-4cce-4899-95c0-42f60fab8a6e
-- title:
--   Proposition 2.9 — $\Phi_B$ is CPTP and fixes $\sigma_\beta$; $\mathcal L_\ell$ satisfies KMS detailed balance
-- statement:
--   Let $\sigma_\beta$ be the Gibbs state of $H=\sum_i h^{(i)}_{i,i+1}$ on the periodic chain, $\beta\ge0$, and let $\ell\ge1$.
--
--   1. For every set of sites $B$, the Petz update $\Phi_B$ is a quantum channel (CPTP) and $\Phi_B(\sigma_\beta)=\sigma_\beta$.
--   2. Consequently $\mathcal L_\ell(\sigma_\beta)=0$.
--   3. $\mathcal L_\ell$ generates a CPTP semigroup: $e^{t\mathcal L_\ell}$ is a channel for every $t\ge0$.
--   4. Each $\Phi_B$ is KMS-reversible with respect to $\sigma_\beta$: with $\Gamma_\sigma(X)=\sigma_\beta^{1/2}X\sigma_\beta^{1/2}$,
--   $$
--   \Gamma_\sigma^{-1}\circ\Phi_B\circ\Gamma_\sigma=\Phi_B^\dagger .
--   $$
--   5. Hence $\mathcal L_\ell$ satisfies KMS detailed balance: $\Gamma_\sigma^{-1}\circ\mathcal L_\ell\circ\Gamma_\sigma=\mathcal L_\ell^\dagger$.
--
--   This makes $\sigma_\beta$ a stationary state of the dynamics and identifies $\mathcal L_\ell$ as a KMS-detailed-balanced Lindbladian.
--
--   **Formalization Note** CPTP maps are stated in Kraus form; the adjoint $\dagger$ is the Hilbert–Schmidt adjoint $\operatorname{tr}[\Phi(\rho)A]=\operatorname{tr}[\rho\Phi^\dagger(A)]$ of (37).
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - generalization: every block B (a cyclic interval of length ℓ) and 1 ≤ ℓ < n → every finite set of sites B, every ℓ ≥ 1 and every n; reason: the proof never uses that B is an interval or that ℓ < n; the paper's blocks are among these sets
--   - encoding: CPTP, the semigroup e^{tL}, KMS as equalities of maps → IsChannel (Kraus form), QDSGibbs.sexp, pointwise equalities kmsInv σ (Φ (kmsMap σ X)) = heisAdj Φ X; reason: Lean convention; Kraus form is equivalent to CPTP in finite dimension
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 2.9, p.14; proof pp.14–15, (32)–(36)

import Mathlib
import Definitions.Def_PetzMix_heatBathGen
import Definitions.Def_QDSGibbs_IsChannel

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Proposition 2.9 (KMS-detailed-balanced condition of `L_ℓ`)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 2.9, p.14;
proof pp.14–15, (35)–(36)). For every block `B`, the map `Φ_B` is CPTP and `Φ_B(σ_β) = σ_β`.
Consequently `L_ℓ(σ_β) = 0`, and `L_ℓ` generates a CPTP semigroup `e^{tL_ℓ}`. Moreover each `Φ_B` is
KMS-reversible with respect to `σ_β`, `Γ_σ^{−1} ∘ Φ_B ∘ Γ_σ = Φ_B†`, and hence
`Γ_σ^{−1} ∘ L_ℓ ∘ Γ_σ = L_ℓ†`.

**Formalization Note** Stated for every finite set `B` of sites (the proof never uses that `B` is
an interval) and every `ℓ ≥ 1` and `n`. CPTP is the public Kraus-form `QDSGibbs.IsChannel`, the
semigroup is `QDSGibbs.sexp`, the Hilbert–Schmidt adjoint of (37) is `QDSGibbs.heisAdj`, and
`Γ_σ(X) = σ^{1/2} X σ^{1/2}`. -/
theorem proposition_2_9 (n d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (h : Fin n → ChainOp n d)
    (hh : IsPeriodicNN h) (hnorm : ∀ i, opNorm (h i) ≤ 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ B : Finset (Fin n),
        IsChannel (petzUpdate (gibbs β (∑ i, h i)) B) ∧
        petzUpdate (gibbs β (∑ i, h i)) B (gibbs β (∑ i, h i)) = gibbs β (∑ i, h i) ∧
        ∀ X : ChainOp n d,
          kmsInv (gibbs β (∑ i, h i)) (petzUpdate (gibbs β (∑ i, h i)) B (kmsMap (gibbs β (∑ i, h i)) X)) =
            heisAdj (petzUpdate (gibbs β (∑ i, h i)) B) X) ∧
    heatBathGen β h ℓ (gibbs β (∑ i, h i)) = 0 ∧
    (∀ t : ℝ, 0 ≤ t → IsChannel (sexp (heatBathGen β h ℓ) t)) ∧
    (∀ X : ChainOp n d,
      kmsInv (gibbs β (∑ i, h i)) (heatBathGen β h ℓ (kmsMap (gibbs β (∑ i, h i)) X)) =
        heisAdj (heatBathGen β h ℓ) X) := by sorry

end PetzMix
