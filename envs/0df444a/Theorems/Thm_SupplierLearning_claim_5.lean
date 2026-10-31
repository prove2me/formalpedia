-- Prove2me | Theorems.Thm_SupplierLearning_claim_5
-- name    : SupplierLearning.claim_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:12.886801+00:00
-- url     : https://prove2.me/theorems/5e5b9f7d-efb3-4b90-995f-3595f18b941c
-- title:
--   Claim 5 — when supplier-$\ell0$ lies again (corrected: with IC$^{h1}$ binding and $q_2^{h1}\ge q_2^{h0}$)
-- statement:
--   Let $t$ be a term with $q_2^{h1}\ge q_2^{h0}$ on which (IC$^{h1}$) binds: $p_2^{h1}-(c^h-r^hq_1^h)q_2^{h1}=p_2^{h0}-(c^h-r^hq_1^h)q_2^{h0}$. Consider a supplier of type $\ell$ with outcome $\Lambda=0$ who has picked this term. If $c^\ell\ge c^h-r^hq_1^h$ he (weakly) prefers the truth $\tilde\Lambda=0$; otherwise he (weakly) prefers to lie again, $\tilde\Lambda=1$, and strictly so when $q_2^{h1}>q_2^{h0}$.
--
--   This is what separates the two lines of (4).
--
--   Differences from the source:
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive, and the standing assumptions of §2 → any real parameters, with no standing assumption; reason: the argument is one line of algebra that uses none of them; the paper's parameters are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - correction: Claim 5 rests on Claim 4 and says supplier-ℓ0 will lie again when c^ℓ < c^h − r^h q₁^h → hypotheses: IC^{h1} binds and q₂^{h1} ≥ q₂^{h0}; "lies again" weakly, and strictly when q₂^{h1} > q₂^{h0}; reason: Claim 4 is false as printed, so IC^{h1} binding is assumed rather than derived; q₂^{h1} ≥ q₂^{h0} is Claim 2; at q₂^{h1} = q₂^{h0} the supplier is indifferent
--   - generalization: a feasible contract → any term t on which IC^{h1} binds; reason: feasibility is not used, and a feasible contract's term is a special case
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 5, App. p.6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Term
import Definitions.Def_SupplierLearning_Params_stagePayoff

namespace SupplierLearning

/-- **Claim 5 — when supplier-ℓ0 lies again (corrected: with IC^{h1} binding and q_2^{h1}≥ q_2^{h0}).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Claim 5, App. p.6 (PDF p.38).

**Formalization Note.** The claim needs (IC^{h1}) binding, which the paper gets from Claim 4 and which is assumed here, and `q₂^{h1} ≥ q₂^{h0}` (Claim 2). "Lies again" is stated weakly for `q₂^{h1} ≥ q₂^{h0}` and strictly when `q₂^{h1} > q₂^{h0}`: at equal quantities the supplier is indifferent. -/
theorem claim_5 (P : Params) (t : Term)
    (hbind : P.stagePayoff .h true t true = P.stagePayoff .h true t false)
    (hx : t.q₂ false ≤ t.q₂ true) :
    (P.ch - P.rh * t.q₁ ≤ P.cl → P.stagePayoff .l false t true ≤ P.stagePayoff .l false t false) ∧
    (P.cl < P.ch - P.rh * t.q₁ →
      P.stagePayoff .l false t false ≤ P.stagePayoff .l false t true ∧
        (t.q₂ false < t.q₂ true → P.stagePayoff .l false t false < P.stagePayoff .l false t true)) := by sorry

end SupplierLearning
