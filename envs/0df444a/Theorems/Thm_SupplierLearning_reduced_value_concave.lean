-- Prove2me | Theorems.Thm_SupplierLearning_reduced_value_concave
-- name    : SupplierLearning.reduced_value_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:42.802094+00:00
-- url     : https://prove2.me/theorems/17c8100d-e07b-4b30-ac1c-380e4195a5b3
-- title:
--   Step 3 — $F$ is continuous at the kink, piecewise quadratic and strictly concave (corrected: also covers the pooled piece)
-- statement:
--   Assume the second-order conditions. Then $F$ is continuous at $\Delta c_1/r^h$ and strictly concave on $[0,Q]$. Further, $F$ is a concave quadratic on each of the following pieces:
--
--   1. if $r^h>\nu r^\ell$: on $[0,q_p]$, on $[q_p,\Delta c_1/r^h]$ and on $[\Delta c_1/r^h,\infty)$;
--   2. if $r^h\le\nu r^\ell$: on $[0,\infty)$.
--
--   This is the concavity that makes the optimal first-period quantity unique.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: (A3): F is concave quadratic on both regions → SecondOrder: (A3) when r^h > ν r^ℓ, and δρ²B² < 4 when r^h ≤ ν r^ℓ; reason: (A3) concerns the separating pieces only; when r^h ≤ ν r^ℓ the objective is one pooled quadratic, which is unbounded if δρ²B² ≥ 4
--   - correction: two regions, split at Δc₁/r^h → three pieces when r^h > ν r^ℓ, split at q_p and Δc₁/r^h, and one when r^h ≤ ν r^ℓ; reason: the selected second-period quantities pool on [0, q_p], so F is not one quadratic on the left region
--   - encoding: F(q) ≡ max over q₂^{h1}, q₂^{h0} → F defined by the explicit reduced formula; reason: period_two_single and period_two_double show it is the maximum; a real supremum would be junk on unbounded sets
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. pp.7–8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_SecondOrder
import Definitions.Def_SupplierLearning_Params_reducedValue
import Definitions.Def_SupplierLearning_Params_kinkPoint
import Definitions.Def_SupplierLearning_Params_poolingThreshold
import Definitions.Def_SupplierLearning_Params_capacityDomain

namespace SupplierLearning

/-- **Step 3 — F is continuous at the kink, piecewise quadratic and strictly concave (corrected: also covers the pooled piece).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. pp.7–8 (PDF p.39, 40).

**Formalization Note.** `F` has up to three pieces when `r^h > ν r^ℓ`: pooled on `[0, q_p]`, double-deviation separating on `[q_p, Δc₁/r^h]`, single-deviation separating beyond. When `r^h ≤ ν r^ℓ` it is one pooled piece. The paper's "two regions" and (A3) concern only the separating pieces; the pooled piece has curvature `δρ²B²`, which (A3) controls when `r^h > ν r^ℓ` and `SecondOrder` controls otherwise. -/
theorem reduced_value_concave (P : Params) (hP : P.Standing) (hSO : P.SecondOrder) :
    ContinuousAt P.reducedValue P.kinkPoint ∧
    StrictConcaveOn ℝ P.capacityDomain P.reducedValue ∧
    (P.ν * P.rl < P.rh →
      (∃ a b c : ℝ, a < 0 ∧ ∀ q, 0 ≤ q → q ≤ P.poolingThreshold →
        P.reducedValue q = a * q ^ 2 + b * q + c) ∧
      (∃ a b c : ℝ, a < 0 ∧ ∀ q, P.poolingThreshold ≤ q → q ≤ P.kinkPoint →
        P.reducedValue q = a * q ^ 2 + b * q + c) ∧
      (∃ a b c : ℝ, a < 0 ∧ ∀ q, P.kinkPoint ≤ q →
        P.reducedValue q = a * q ^ 2 + b * q + c)) ∧
    (P.rh ≤ P.ν * P.rl →
      ∃ a b c : ℝ, a < 0 ∧ ∀ q, 0 ≤ q → P.reducedValue q = a * q ^ 2 + b * q + c) := by sorry

end SupplierLearning
