-- Prove2me | Theorems.Thm_SupplierLearning_period_two_single
-- name    : SupplierLearning.period_two_single
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:44.268394+00:00
-- url     : https://prove2.me/theorems/c9567d9e-433d-447f-97d6-64afdd74f414
-- title:
--   Step 2, case $c^h-r^hq\le c^\ell$ — separating or pooling period-2 output
-- statement:
--   Fix $q$ with $c^h-r^hq\le c^\ell$ (so $q\ge\Delta c_1/r^h>0$). If $\bar y(q)>\bar z(q)$ then $(\bar y(q),\bar z(q))$ is the unique maximizer of $H(q,\cdot,\cdot)$ on $\{y\ge z\}$; otherwise $(\hat y(q),\hat y(q))$ is. Moreover
--   $$
--   \bar y(q)>\bar z(q)\iff r^h>\nu r^\ell.
--   $$
--   This is the separating/pooling dichotomy of Proposition 1(b) under single deviation.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: the buyer's FOCs characterize the optimal production → the unique maximizer of H(q, ·, ·) on {y ≥ z} for fixed q; reason: q₂^{h1} ≥ q₂^{h0} by Claim 2, and a maximizer is what the proof uses
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. pp.6–7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_separatingHigh
import Definitions.Def_SupplierLearning_Params_separatingLow
import Definitions.Def_SupplierLearning_Params_poolingQuantity
import Definitions.Def_SupplierLearning_Params_IsPeriodTwoMax

namespace SupplierLearning

/-- **Step 2, case c^h-r^hq≤ c^ℓ — separating or pooling period-2 output.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. pp.6–7 (PDF p.38, 39).

**Formalization Note.** For fixed `q` in the case `c^h − r^h q ≤ c^ℓ`. That case forces `r^h q ≥ Δc₁ > 0`, so `q > 0`, which the equivalence with `r^h > ν r^ℓ` uses, is not a separate hypothesis. -/
theorem period_two_single (P : Params) (hP : P.Standing) {q : ℝ}
    (hk : P.ch - P.rh * q ≤ P.cl) :
    (P.separatingLow q < P.separatingHigh q →
      P.IsPeriodTwoMax q (P.separatingHigh q) (P.separatingLow q)) ∧
    (P.separatingHigh q ≤ P.separatingLow q →
      P.IsPeriodTwoMax q (P.poolingQuantity q) (P.poolingQuantity q)) ∧
    (P.separatingLow q < P.separatingHigh q ↔ P.ν * P.rl < P.rh) := by sorry

end SupplierLearning
