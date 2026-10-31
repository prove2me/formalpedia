-- Prove2me | Theorems.Thm_SupplierLearning_lowest_rent
-- name    : SupplierLearning.lowest_rent
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:24.945923+00:00
-- url     : https://prove2.me/theorems/0490f32a-8fbc-442e-bc0c-2c96ae96bfcf
-- title:
--   The lowest information rent, and the reduced type-$h$ problem
-- statement:
--   Let $\phi\in\Phi$, with $v^h=(q_1^h,q_2^{h1},q_2^{h0})$. Then
--   $$
--   U(h)+\Gamma^+(v^h)\le\tilde U(\ell;h)\le U(\ell),
--   $$
--   and hence
--   $$
--   \tilde V(\phi)\le\nu\big[W_\ell(v^\ell)-\Gamma^+(v^h)\big]+(1-\nu)W_h(v^h)-U(h).
--   $$
--   So every feasible contract pays type $\ell$ at least the rent (20), and the type-$h$ quantities solve the problem $\max H(v)=W_h(v)-\kappa\Gamma^+(v)$.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - reading: By IC^ℓ this is the lowest information rent, stated for the deferred payment scheme → for every feasible contract, U(ℓ) − U(h) ≥ Γ⁺(v^h), the single formula for (20); reason: "lowest" is a claim about all feasible contracts, and the paper's route through Claim 4 fails
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, after (20), App. p.6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_buyerPayoff
import Definitions.Def_SupplierLearning_Params_typeSurplus
import Definitions.Def_SupplierLearning_Params_rentBound

namespace SupplierLearning

/-- **The lowest information rent, and the reduced type-h problem.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, after (20), App. p.6 (PDF p.38).

**Formalization Note.** `q₁^h = 0` is included. There `y < z` is possible, and `Ũ(ℓ; h) − U(h)` still dominates `Γ⁺`. -/
theorem lowest_rent (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ) :
    P.U φ .h + P.rentBound (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) ≤
      P.supplierPayoff φ .l .h ∧
    P.supplierPayoff φ .l .h ≤ P.U φ .l ∧
    P.buyerPayoff φ ≤
      P.ν * (P.typeSurplus .l (φ .l).q₁ ((φ .l).q₂ true) ((φ .l).q₂ false) -
          P.rentBound (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false)) +
        (1 - P.ν) * P.typeSurplus .h (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) - P.U φ .h := by sorry

end SupplierLearning
