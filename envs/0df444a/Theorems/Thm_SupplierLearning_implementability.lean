-- Prove2me | Theorems.Thm_SupplierLearning_implementability
-- name    : SupplierLearning.implementability
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:25.808353+00:00
-- url     : https://prove2.me/theorems/7fffed90-ecaf-41a1-9da0-b97e94f148d3
-- title:
--   Implementability of the corrected contract (not in the paper): $\tilde U(h;\ell)\le0$ at $\phi^*$
-- statement:
--   **This statement is not in the paper.** It closes a gap in the proof of Proposition 1, which never checks (IC$^h$).
--
--   Under the hypotheses of the goal, type $h$ does not want type $\ell$'s corrected term: $\tilde U(h;\ell)\le0$ at $\phi^*$. Equivalently, with $(q^\ell,y^\ell,z^\ell)$ the first-best quantities of type $\ell$,
--   $$
--   U^\ell(q,y,z)\le\Gamma(q^\ell,y^\ell,z^\ell)-\delta\rho\max\{0,(\Delta c_1-r^hq^\ell)(y^\ell-z^\ell)\}.
--   $$
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: no statement: the proof of Proposition 1 does not check IC^h → a new lemma, under the hypotheses of the goal; reason: IC^h is a constraint of Φ, and it fails for the printed payment: at a₁ = a₂ = 100, c^ℓ = 10, c^h = 11, r^θ = 1, δ = ρ = ν = 1/2 one has Ũ(h; ℓ) = 49/10
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, gap in the proof of Proposition 1, App. pp.5–8; constraint (IC^θ), p.8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo
import Definitions.Def_SupplierLearning_Params_rent
import Definitions.Def_SupplierLearning_Params_Candidate
import Definitions.Def_SupplierLearning_Params_SecondOrder
import Definitions.Def_SupplierLearning_Params_FirstBestAdmissible
import Definitions.Def_SupplierLearning_Params_contractStar
import Definitions.Def_SupplierLearning_Params_rentFloor

namespace SupplierLearning

/-- **Implementability of the corrected contract (not in the paper): Ũ(h;ℓ)≤0 at φ^*.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, gap in the proof of Proposition 1, App. pp.5–8; constraint (IC^θ), p.8 (PDF p.37–40, 8).

**Formalization Note.** **This statement is not in the paper.** The paper's proof never checks (IC^h). The planning session found the proof; the argument compares `v` with `v^ℓ` or with `(q^ℓ, z^ℓ, z^ℓ)` by optimality of `v` for `H` and of `v^ℓ` for `W_ℓ`. -/
theorem implementability (P : Params) (hP : P.Standing) (hSO : P.SecondOrder)
    (hFB : P.FirstBestAdmissible) {q y z : ℝ} (hC : P.Candidate q y z) :
    P.supplierPayoff (P.contractStar q y z) .h .l ≤ 0 ∧
    P.rent q y z ≤
      P.rentFloor (P.firstBestOne .l) (P.firstBestTwo .l true) (P.firstBestTwo .l false) -
        P.δ * P.ρ * max 0 ((P.deltaC - P.rh * P.firstBestOne .l) *
          (P.firstBestTwo .l true - P.firstBestTwo .l false)) := by sorry

end SupplierLearning
