-- Prove2me | Theorems.Thm_SupplierLearning_deferred_payment
-- name    : SupplierLearning.deferred_payment
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:41.433402+00:00
-- url     : https://prove2.me/theorems/d2bdb9e5-6990-424c-9cd6-bd74a99e9c83
-- title:
--   Eqs. (19)–(20) — the deferred payment and the deviation payoff (corrected: states $q_2^{h1}\ge q_2^{h0}$ and (C))
-- statement:
--   Let $q\ge0$ with Condition (C), let $y\ge z$, and let $\phi$ be any contract whose type-$h$ term is the deferred payment (19). Then $U(h)=0$, (IC$^{h1}$) and (IC$^{h0}$) hold, and the deviation payoff of type $\ell$ is (20):
--   $$
--   \tilde U(\ell;h)=\begin{cases}\Delta c_1q+\delta\Delta c_1[\rho y+(1-\rho)z]+\delta\rho(r^\ell-r^h)qy,& c^h-r^hq\le c^\ell,\\ \Delta c_1q+\delta\Delta c_1y+\delta\rho(r^\ell-r^h)qy-\delta(1-\rho)r^hq(y-z),& c^h-r^hq>c^\ell.\end{cases}
--   $$
--   This is how the rent (4) arises.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: the deferred payment scheme is stated with no conditions on q₁^h, q₂^{h1}, q₂^{h0} → hypotheses 0 ≤ q, z ≤ y and (C); reason: IC^{h0} needs r^h q (y − z) ≥ 0, and (20) needs (C) for supplier-ℓ1's report; these fail outside the hypotheses, e.g. y < z with q > 0
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, (19)–(20), App. p.6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_stagePayoff
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_rent
import Definitions.Def_SupplierLearning_Params_deferredTerm

namespace SupplierLearning

/-- **Eqs. (19)–(20) — the deferred payment and the deviation payoff (corrected: states q_2^{h1}≥ q_2^{h0} and (C)).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, (19)–(20), App. p.6 (PDF p.38).

**Formalization Note.** "Feasible" on the page means the three named constraints. `P.U φ .h = 0` gives IR^h. Right side: (20), the same formula as (4). -/
theorem deferred_payment (P : Params) (hP : P.Standing) {q y z : ℝ} (hq : 0 ≤ q) (hzy : z ≤ y)
    (hcap : (P.rh - P.rl) * q ≤ P.ch - P.cl) {φ : Contract} (hφ : φ .h = P.deferredTerm q y z) :
    P.U φ .h = 0 ∧
    P.stagePayoff .h true (φ .h) false ≤ P.stagePayoff .h true (φ .h) true ∧
    P.stagePayoff .h false (φ .h) true ≤ P.stagePayoff .h false (φ .h) false ∧
    P.supplierPayoff φ .l .h = P.rent q y z := by sorry

end SupplierLearning
