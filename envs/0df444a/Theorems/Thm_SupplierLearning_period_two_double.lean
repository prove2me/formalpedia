-- Prove2me | Theorems.Thm_SupplierLearning_period_two_double
-- name    : SupplierLearning.period_two_double
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:53.256496+00:00
-- url     : https://prove2.me/theorems/2c96e49b-8d04-48a1-af41-275e36932270
-- title:
--   Step 2, case $c^h-r^hq>c^\ell$ — separating or pooling period-2 output under double deviation
-- statement:
--   Fix $q\ge0$ with $c^h-r^hq>c^\ell$. If $\bar y(q)>\bar z(q)$ then $(\bar y(q),\bar z(q))$ is the unique maximizer of $H(q,\cdot,\cdot)$ on $\{y\ge z\}$; otherwise $(\hat y(q),\hat y(q))$ is, with the same $\hat y$ as in the case $c^h-r^hq\le c^\ell$. Moreover
--   $$
--   \rho\,\bar y(q)+(1-\rho)\,\bar z(q)=\hat y(q).
--   $$
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: the buyer's FOCs characterize the optimal production → the unique maximizer of H(q, ·, ·) on {y ≥ z} for fixed q; reason: q₂^{h1} ≥ q₂^{h0} by Claim 2, and a maximizer is what the proof uses
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_separatingHigh
import Definitions.Def_SupplierLearning_Params_separatingLow
import Definitions.Def_SupplierLearning_Params_poolingQuantity
import Definitions.Def_SupplierLearning_Params_IsPeriodTwoMax

namespace SupplierLearning

/-- **Step 2, case c^h-r^hq>c^ℓ — separating or pooling period-2 output under double deviation.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.7 (PDF p.39).

**Formalization Note.** Uses the double-deviation forms of App. p.7, not note 9. The last clause is the fact behind "the pooling contract equals that for `c^h − r^h q₁^h ≤ c^ℓ`": the pooling quantity is the `ρ`-average of the separating ones. -/
theorem period_two_double (P : Params) (hP : P.Standing) {q : ℝ} (hq : 0 ≤ q)
    (hk : P.cl < P.ch - P.rh * q) :
    (P.separatingLow q < P.separatingHigh q →
      P.IsPeriodTwoMax q (P.separatingHigh q) (P.separatingLow q)) ∧
    (P.separatingHigh q ≤ P.separatingLow q →
      P.IsPeriodTwoMax q (P.poolingQuantity q) (P.poolingQuantity q)) ∧
    P.ρ * P.separatingHigh q + (1 - P.ρ) * P.separatingLow q = P.poolingQuantity q := by sorry

end SupplierLearning
