-- Prove2me | Theorems.Thm_SupplierLearning_claim_3
-- name    : SupplierLearning.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:49.104878+00:00
-- url     : https://prove2.me/theorems/d707bb2b-4b02-4142-95f1-c548a1f35575
-- title:
--   Claim 3 — after lying about $\theta$, supplier-$\ell1$ reports truthfully (corrected: for $q_1^h>0$)
-- statement:
--   Let $\phi\in\Phi$ with $q_1^h>0$. A supplier of type $\ell$ with outcome $\Lambda=1$ who has picked type $h$'s term prefers to report $\tilde\Lambda=1$:
--   $$
--   p_2^{h1}-(c^\ell-r^\ell q_1^h)q_2^{h1}\ge p_2^{h0}-(c^\ell-r^\ell q_1^h)q_2^{h0}.
--   $$
--   This removes one of the two branches of the deviating supplier's period-2 decision.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: supplier-ℓ1 tells the truth after the lie θ̃ = h, for every feasible contract → hypothesis 0 < q₁^h; reason: false at q₁^h = 0 with q₂^{h1} < q₂^{h0}, where Claim 2 fails: there p₂^{h1} − p₂^{h0} = c^h(q₂^{h1} − q₂^{h0}) < c^ℓ(q₂^{h1} − q₂^{h0})
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 3, App. p.5

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_stagePayoff
import Definitions.Def_SupplierLearning_Params_Feasible

namespace SupplierLearning

/-- **Claim 3 — after lying about θ, supplier-ℓ1 reports truthfully (corrected: for q_1^h>0).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 3, App. p.5 (PDF p.37).

**Formalization Note.** `0 < q₁^h` is added because the proof uses Claim 2. When `q₁^h = 0` and `q₂^{h1} < q₂^{h0}` the conclusion fails. -/
theorem claim_3 (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (hq : 0 < (φ .h).q₁) :
    P.stagePayoff .l true (φ .h) false ≤ P.stagePayoff .l true (φ .h) true := by sorry

end SupplierLearning
