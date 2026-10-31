-- Prove2me | Theorems.Thm_SupplierLearning_claim_2
-- name    : SupplierLearning.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:57.760616+00:00
-- url     : https://prove2.me/theorems/137d37c0-774a-47fa-a508-d51df9cd91d0
-- title:
--   Claim 2 — $q_2^{\theta1}\ge q_2^{\theta0}$ (corrected: for $q_1^\theta>0$)
-- statement:
--   Let $\phi\in\Phi$ and let $\theta$ be a type with $q_1^\theta>0$. Then
--   $$
--   q_2^{\theta1}\ge q_2^{\theta0}.
--   $$
--   This is the monotonicity of second-period output in the learning outcome. It is what makes the second-period domain $\{y\ge z\}$.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: q₂^{θ1} ≥ q₂^{θ0} for every feasible contract → hypothesis 0 < q₁^θ; reason: false at q₁^θ = 0: IC^{θ1} and IC^{θ0} both say p₂^{θ1} − c^θ q₂^{θ1} = p₂^{θ0} − c^θ q₂^{θ0}, which permits q₂^{θ1} < q₂^{θ0}
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 2, App. p.5

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_Feasible

namespace SupplierLearning

/-- **Claim 2 — q_2^{θ1}≥ q_2^{θ0} (corrected: for q_1^θ>0).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 2, App. p.5 (PDF p.37).

**Formalization Note.** At `q₁^θ = 0` the two constraints collapse to one equation and the inequality can fail, so `0 < q₁^θ` is added. -/
theorem claim_2 (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (θ : SupplierType) (hq : 0 < (φ θ).q₁) :
    (φ θ).q₂ false ≤ (φ θ).q₂ true := by sorry

end SupplierLearning
