-- Prove2me | Theorems.Thm_SupplierLearning_claim_4
-- name    : SupplierLearning.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:45.582996+00:00
-- url     : https://prove2.me/theorems/265b9ab2-976a-4904-b12b-c6489dc60058
-- title:
--   Claim 4 (corrected: the rent bound is attained with IC$^{h1}$ binding)
-- statement:
--   Let $\phi\in\Phi$ with $q=q_1^h>0$, write $y=q_2^{h1}$, $z=q_2^{h0}$, $x=y-z$ and $D=p_2^{h1}-p_2^{h0}$. Then
--
--   1. (IC$^{h1}$) and (IC$^{h0}$) give $(c^h-r^hq)x\le D\le c^hx$;
--   2. $\tilde U(\ell;h)-U(h)=\Delta c_1q+\delta\rho(\Delta c_1+\Delta r\,q)y+\delta(1-\rho)\big[\Delta c_1z+\max\{0,D-c^\ell x\}\big]$;
--   3. this difference is at least $\Gamma^+(q,y,z)$;
--   4. it equals $\Gamma^+(q,y,z)$ when $D=(c^h-r^hq)x$, i.e. when (IC$^{h1}$) binds.
--
--   So the deviation payoff is smallest with (IC$^{h1}$) binding, which is what the deferred payment achieves.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: at the optimum IC^{h1} is binding and IC^{h0} is slack → for every φ ∈ Φ with 0 < q₁^h (Claim 3 needs it), the rent difference is bounded below by Γ⁺, with equality when IC^{h1} binds; reason: false as printed: under single deviation any transfer gap D between (c^h − r^h q)x and c^ℓ x gives the same rent, so an optimal contract can have IC^{h1} slack; in the printed perturbation ΔŨ = 0 when 𝟙_Λ = 0
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 4, App. pp.5–6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_rentBound

namespace SupplierLearning

/-- **Claim 4 (corrected: the rent bound is attained with IC^{h1} binding).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 4, App. pp.5–6 (PDF p.37, 38).

**Formalization Note.** The printed claim that IC^{h1} must bind at every optimum is false. Under single deviation every `D` between `(c^h − r^h q)x` and `c^ℓ x` gives the same rent: in the C1 instance of `paper.md`, with `c^h − r^h q = −41.8 ≤ c^ℓ = 10`, replacing `p₂^{h1} − p₂^{h0}` by any `D` in that band while keeping `U(h)` gives another optimal contract, with IC^{h1} slack. This statement is what is true: the rent is smallest at `D = (c^h − r^h q)x`. -/
theorem claim_4 (P : Params) (hP : P.Standing) {φ : Contract} (hφ : P.Feasible φ)
    (hq : 0 < (φ .h).q₁) :
    let q := (φ .h).q₁
    let y := (φ .h).q₂ true
    let z := (φ .h).q₂ false
    let x := y - z
    let D := (φ .h).p₂ true - (φ .h).p₂ false
    (P.ch - P.rh * q) * x ≤ D ∧ D ≤ P.ch * x ∧
    P.supplierPayoff φ .l .h - P.U φ .h =
      P.deltaC * q + P.δ * P.ρ * (P.deltaC + P.deltaR * q) * y +
        P.δ * (1 - P.ρ) * (P.deltaC * z + max 0 (D - P.cl * x)) ∧
    P.rentBound q y z ≤ P.supplierPayoff φ .l .h - P.U φ .h ∧
    (D = (P.ch - P.rh * q) * x → P.supplierPayoff φ .l .h - P.U φ .h = P.rentBound q y z) := by sorry

end SupplierLearning
