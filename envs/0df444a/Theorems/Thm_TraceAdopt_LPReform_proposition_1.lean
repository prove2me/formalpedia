-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_proposition_1
-- name    : TraceAdopt.LPReform.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:05.386838+00:00
-- url     : https://prove2.me/theorems/86d47b42-1dc0-41b8-9228-371642dc8f18
-- title:
--   Proposition 1, p. 10 — SCTM firm states agree with even-time LTM firm states
-- statement:
--   Begin the SCTM process on $G$ and the weighted LTM process on $G'$ from the same set $S_0$ of active firms, with no supply-chain vertex initially active. For every time $t\ge0$, the firms active after $t$ SCTM steps are exactly the firms active after $2t$ LTM steps:
--
--   $$S_t=S'_{2t}\cap N_F.$$
--
--   A firm eventually activates under SCTM if and only if its corresponding vertex eventually activates under LTM. This is Proposition 1's equality of the final firm sets.
--
--   **Formalization Note** The standing assumptions include positive adoption costs, thresholds at least two, total benefit sufficient for activation, and connectedness. Time zero is included.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 10, Proposition 1; p. 34, proof

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

/-- Proposition 1, p. 10: the firm states agree at even LTM times, and the
eventually active firms agree. -/
theorem proposition_1 (I : Instance) (hI : I.Standing)
    (S₀ : Finset (Fin I.n)) :
    (∀ t : ℕ, ∀ i : Fin I.n,
      i ∈ (step I)^[t] S₀ ↔
        Sum.inl i ∈ (ltmStep I)^[2 * t] (liftSeeds I S₀)) ∧
    (∀ i : Fin I.n,
      (∃ t : ℕ, i ∈ (step I)^[t] S₀) ↔
        ∃ t : ℕ, Sum.inl i ∈ (ltmStep I)^[t] (liftSeeds I S₀)) := by sorry

end TraceAdopt.LPReform
