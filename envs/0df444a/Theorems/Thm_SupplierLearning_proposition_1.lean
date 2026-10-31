-- Prove2me | Theorems.Thm_SupplierLearning_proposition_1
-- name    : SupplierLearning.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:53:30.847427+00:00
-- url     : https://prove2.me/theorems/52d32f6c-6503-404d-9073-e4c4be57e2b6
-- title:
--   Proposition 1 (corrected: IC$^h$-compatible payment, second-order and interiority hypotheses, double-deviation forms, kink inequalities) — the optimal contract in regime $\mathcal P^{\mathrm{AL}}$
-- statement:
--   Assume the standing assumptions and the second-order conditions, assume type $\ell$'s first best is admissible, and let $(q,y,z)$ be a candidate for type $h$'s quantities. So $(y,z)=(\bar y(q),\bar z(q))$ if $\bar y(q)>\bar z(q)$, $y=z=\hat y(q)$ otherwise, and $q$ satisfies the first-order condition. Let $\phi^*$ be the contract in which type $\ell$ has its first best $(q^\ell,y^\ell,z^\ell)$ and payments
--   $$
--   p_1^\ell=c^\ell q^\ell-\delta\rho r^\ell q^\ell y^\ell+U^\ell,\quad p_2^{\ell1}=(c^\ell-r^\ell q^\ell)y^\ell+r^\ell q^\ell y^\ell,\quad p_2^{\ell0}=c^\ell z^\ell,
--   $$
--   and type $h$ has the deferred payment
--   $$
--   p_1^h=c^hq-\delta\rho r^hqz,\quad p_2^{h1}=(c^h-r^hq)y+r^hqz,\quad p_2^{h0}=c^hz.
--   $$
--   Then:
--
--   1. $\phi^*$ is feasible and optimal.
--   2. $U(h)=0$ and $U(\ell)=U^\ell(q,y,z)>0$, where $U^\ell$ is the rent (4).
--   3. Every optimal contract has exactly the quantities of $\phi^*$, and has $U(h)=0$ and $U(\ell)=U^\ell(q,y,z)$.
--   4. If $r^hq\ne\Delta c_1$, then
--   $$
--   q=\frac{a_1-c^h}{2}+\frac\delta2\rho r^hy-\frac12\frac{\nu}{1-\nu}\frac{\partial U^\ell}{\partial q_1^h},
--   $$
--   with $\partial U^\ell/\partial q_1^h$ as in (21).
--   5. The contract with the printed payments to type $\ell$ (with $z^\ell$ in place of $y^\ell$ in the two learning terms) is feasible if and only if $U^\ell(q,y,z)\le\Delta c_1q^\ell+\delta\Delta c_1z^\ell+\delta\rho q^\ell z^\ell\Delta r$, and in that case it is optimal.
--
--   The printed proposition is false in several ways, listed below; its quantities, rents and value survive. The contract pays type $\ell$ a rent with a learning term $\delta\rho qy\Delta r$ of either sign, and two regimes arise, according to whether a learned type $h$ can undercut an unlearned type $\ell$.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - reading: production quantities with no stated sign → all quantities ≥ 0 in Params.Feasible; reason: they are production quantities
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: Proposition 1(a) for θ = ℓ: p₁^ℓ, p₂^{ℓ1} with q₂^{ℓ0} in the two learning terms → φ* with q₂^{ℓ1} in these terms; clause 5 keeps the printed contract, which is in Φ iff (PR); reason: C1: at a₁ = a₂ = 100, c^ℓ = 10, c^h = 11, r^θ = 1, δ = ρ = ν = 1/2 the printed contract has Ũ(h; ℓ) = 49/10 > 0 = U(h), so it is not in Φ
--   - correction: no second-order condition → (E1) δρ(r^ℓ)² < 4 and (E3) (A3) if r^h > ν r^ℓ, δρ²B² < 4 otherwise (Params.SecondOrder); reason: C2: at a₁ = a₂ = 100, c^ℓ = 10, c^h = 11, r^θ = 3, δ = ρ = 9/10, ν = 1/2 the supremum of Ṽ on Φ is +∞; C6: at a₂ = 60, c^ℓ = 10, c^h = 20, r^θ = 1, δ = 9/10, ρ = 1/10, ν = 1/2 and some a₁ ≈ 45.762 two productions tie
--   - correction: no bound on the optimal quantities → (E2) Params.FirstBestAdmissible and the bounds of Params.Candidate: 0 ≤ q, 0 ≤ z, 0 < q + y, (C); reason: C3: at a₁ = 80, a₂ = 120, δ = 0.9, c^h = 32, c^ℓ = 20, ρ = 0.4, r^ℓ = 0.1, r^h = 0.9, ν = 0.5 the printed condition gives q₁^h ≈ 40.04 but Q = 15
--   - correction: note 9 defines q̄₂^{h1}, q̄₂^{h0} once and for all → the App. p.7 forms when c^h − r^h q > c^ℓ; reason: C4: at a₁ = 80, a₂ = 120, c^ℓ = 25, c^h = 45, r^ℓ = 1/2, r^h = 9/10, δ = 9/10, ρ = 2/5, ν = 1/2 the optimum has q₂^{h1} ≈ 34.79, q₂^{h0} ≈ 29.93, whereas note 9 gives 38.43 and 27.5
--   - correction: the first-order equation for q₁^h at every point → at r^h q = Δc₁ the two one-sided inequalities of Params.Candidate; clause 4 for r^h q ≠ Δc₁; reason: C5: ∂U^ℓ/∂q₁^h does not exist at the kink, and at a₁ = 87 with the other values of C4 the optimum q₁^h = 200/9 equals neither one-sided right side (20.815 and 24.325)
--   - reading: the optimal production is unique → every optimal contract has the quantities of φ*, U(h) = 0 and U(ℓ) = U^ℓ(q, y, z); reason: payments are not unique, as the Claim 4 band shows
--   - encoding: the max in (P^AL); ∂E_{Λ|h}W₂/∂q₁^h and ∂U^ℓ/∂q₁^h → Params.IsOptimal (membership and a universal bound); ρ r^h y and Params.marginalRent; reason: a real supremum is junk on unbounded sets; the paper's ∂ hold q₂^{hΛ} fixed
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1, p.13; note 9, p.26; proof, App. pp.5–8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_kappa
import Definitions.Def_SupplierLearning_Params_U
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_IsOptimal
import Definitions.Def_SupplierLearning_Params_rent
import Definitions.Def_SupplierLearning_Params_marginalRent
import Definitions.Def_SupplierLearning_Params_Candidate
import Definitions.Def_SupplierLearning_Params_SecondOrder
import Definitions.Def_SupplierLearning_Params_FirstBestAdmissible
import Definitions.Def_SupplierLearning_Params_contractStar
import Definitions.Def_SupplierLearning_Params_printedContract
import Definitions.Def_SupplierLearning_Params_PrintedRentCondition

namespace SupplierLearning

/-- **Proposition 1 (corrected: IC^h-compatible payment, second-order and interiority hypotheses, double-deviation forms, kink inequalities) — the optimal contract in regime P^{AL}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1, p.13; note 9, p.26; proof, App. pp.5–8 (PDF p.13, 26, 37–40).

**Formalization Note.** The goal is the printed proposition with corrections C1–C6 of `paper.md`. Clause 1 is the deferred payment of (a) with the payment to type ℓ corrected; the clause for type h's payments is the definition of `contractStar`. Clause 2 is the rent statement of (a) and (4). Clause 3 is "the optimal production is unique" of (b), with type ℓ at first best. Clause 4 is the first-order form of `q₁^{h|AL}` in (b). Clause 5 keeps the printed contract where it is true. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (hSO : P.SecondOrder)
    (hFB : P.FirstBestAdmissible) {q y z : ℝ} (hC : P.Candidate q y z) :
    P.IsOptimal (P.contractStar q y z) ∧
    P.U (P.contractStar q y z) .h = 0 ∧
    P.U (P.contractStar q y z) .l = P.rent q y z ∧
    0 < P.rent q y z ∧
    (∀ φ, P.IsOptimal φ →
      (∀ θ, (φ θ).q₁ = (P.contractStar q y z θ).q₁ ∧
        ∀ Λ, (φ θ).q₂ Λ = (P.contractStar q y z θ).q₂ Λ) ∧
      P.U φ .h = 0 ∧ P.U φ .l = P.rent q y z) ∧
    (P.rh * q ≠ P.ch - P.cl →
      q = (P.a₁ - P.ch) / 2 + P.δ / 2 * (P.ρ * P.rh * y) -
        1 / 2 * P.kappa * P.marginalRent q y z) ∧
    (P.Feasible (P.printedContract q y z) ↔ P.PrintedRentCondition q y z) ∧
    (P.PrintedRentCondition q y z → P.IsOptimal (P.printedContract q y z)) := by sorry

end SupplierLearning
