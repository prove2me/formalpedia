-- Prove2me | Theorems.Thm_SupplierLearning_deviation_payoff
-- name    : SupplierLearning.deviation_payoff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:53:01.129286+00:00
-- url     : https://prove2.me/theorems/bbdb5f8a-e71f-4c72-8c9b-d442b3e779d2
-- title:
--   Deviation payoff $\tilde U(\ell;h)$ after Claim 3 (corrected: for $q_1^h>0$)
-- statement:
--   Let $\phi\in\Phi$ with $q_1^h>0$. The payoff of type $\ell$ from mimicking type $h$ is
--   $$
--   \tilde U(\ell;h)=p_1^h-c^\ell q_1^h+\delta\rho\big[p_2^{h1}-(c^\ell-r^\ell q_1^h)q_2^{h1}\big]+\delta(1-\rho)\max\{p_2^{h1}-c^\ell q_2^{h1},\,p_2^{h0}-c^\ell q_2^{h0}\}.
--   $$
--   Only the branch $\Lambda=0$ keeps a maximum; this is the source of the double deviation.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: the display is stated for the optimum, via Claims 1 and 3 → any feasible contract with hypothesis 0 < q₁^h; reason: Claim 3 is false at q₁^h = 0 with q₂^{h1} < q₂^{h0}; the display uses only Claim 3, not optimality
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, display after Claim 3, App. p.5

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_Feasible

namespace SupplierLearning

/-- **Deviation payoff Ũ(ℓ;h) after Claim 3 (corrected: for q_1^h>0).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, display after Claim 3, App. p.5 (PDF p.37).

**Formalization Note.** `0 < q₁^h` is inherited from Claim 3. -/
theorem deviation_payoff (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (hq : 0 < (φ .h).q₁) :
    P.supplierPayoff φ .l .h =
      (φ .h).p₁ - P.cl * (φ .h).q₁ +
        P.δ * P.ρ * ((φ .h).p₂ true - (P.cl - P.rl * (φ .h).q₁) * (φ .h).q₂ true) +
        P.δ * (1 - P.ρ) *
          max ((φ .h).p₂ true - P.cl * (φ .h).q₂ true) ((φ .h).p₂ false - P.cl * (φ .h).q₂ false) := by sorry

end SupplierLearning
