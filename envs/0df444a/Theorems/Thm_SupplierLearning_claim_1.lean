-- Prove2me | Theorems.Thm_SupplierLearning_claim_1
-- name    : SupplierLearning.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:53:54.085419+00:00
-- url     : https://prove2.me/theorems/e9278a98-93b1-400b-a254-5ac1778c8bbc
-- title:
--   Claim 1 — the chain of rents, and IC$^\ell$, IR$^h$ bind at every optimum
-- statement:
--   Let $\phi\in\Phi$, with quantity vectors $v^\ell$ and $v^h$. Then
--   $$
--   U(\ell)\ge\tilde U(\ell;h)\ge U(h)\ge0,
--   $$
--   and the buyer's payoff decomposes as
--   $$
--   \tilde V(\phi)=\nu\big[W_\ell(v^\ell)-U(\ell)\big]+(1-\nu)\big[W_h(v^h)-U(h)\big].
--   $$
--   If moreover $\phi$ is optimal, then IC$^\ell$ and IR$^h$ bind: $U(h)=0$ and $U(\ell)=\tilde U(\ell;h)$.
--
--   This is the first step of the proof of Proposition 1: the buyer's problem is written as surplus minus rents.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - generalization: the chain U(ℓ) ≥ Ũ(ℓ; h) ≥ U(h) ≥ 0, justified "by c^h ≥ c^ℓ, Condition (C) and optimality", at the optimum → the chain and the decomposition Ṽ = ν[W_ℓ − U(ℓ)] + (1 − ν)[W_h − U(h)] for every φ ∈ Φ; reason: the chain uses only IC^ℓ, IR^h, (C) and q ≥ 0, and an optimal contract is in Φ
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 1, App. p.5

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_buyerPayoff
import Definitions.Def_SupplierLearning_Params_IsOptimal
import Definitions.Def_SupplierLearning_Params_typeSurplus

namespace SupplierLearning

/-- **Claim 1 — the chain of rents, and IC^ℓ, IR^h bind at every optimum.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 1, App. p.5 (PDF p.37).

**Formalization Note.** Claim 1 holds at every optimum with no hypothesis beyond `Params.Standing`. The printed argument for `U(h) = 0` lowers type h's transfers only, which can break (IC^h); lowering the first-period transfers of both types by `U(h)` keeps every constraint, so the conclusion stands. -/
theorem claim_1 (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ) :
    P.supplierPayoff φ .l .h ≤ P.U φ .l ∧
    P.U φ .h ≤ P.supplierPayoff φ .l .h ∧
    0 ≤ P.U φ .h ∧
    P.buyerPayoff φ =
      P.ν * (P.typeSurplus .l (φ .l).q₁ ((φ .l).q₂ true) ((φ .l).q₂ false) - P.U φ .l) +
        (1 - P.ν) * (P.typeSurplus .h (φ .h).q₁ ((φ .h).q₂ true) ((φ .h).q₂ false) - P.U φ .h) ∧
    (P.IsOptimal φ → P.U φ .h = 0 ∧ P.U φ .l = P.supplierPayoff φ .l .h) := by sorry

end SupplierLearning
