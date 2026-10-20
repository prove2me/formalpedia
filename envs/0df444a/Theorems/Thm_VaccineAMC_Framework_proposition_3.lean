-- Prove2me | Theorems.Thm_VaccineAMC_Framework_proposition_3
-- name    : VaccineAMC.Framework.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:24.518017+00:00
-- url     : https://prove2.me/theorems/3a6eecb5-68a0-42aa-9a26-ae087605a3da
-- title:
--   Proposition 3 — a temporary framework AMC leaves capacity unchanged
-- statement:
--   Under the standing assumptions and Assumption 1, fix positive subsidy $s$ and fund $F$. Every equilibrium in which the AMC subsidy is temporary has capacity and both period outputs equal to the no-AMC level:
--
--   $$Q^{\mathrm{TS}}=q^{A}=q^{T}=D(c+\kappa/\beta)=Q^{\mathrm{NA}}=q^{\mathrm{NA}}.$$
--
--   If $sD(c+\kappa/\beta)>rF$, that candidate is itself an equilibrium, establishing existence on the stated temporary branch. Thus an interest-bearing escrow subsidy does not increase a monopolist's capacity incentive when it is exhausted in equilibrium. **Formalization Note** The paper's “temporary subsidy” is read as $sq^A>rF$ at equilibrium. The second clause prevents an empty set of qualifying equilibria from making the statement vacuous.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 13 (PDF 16), Proposition 3

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

namespace VaccineAMC.Framework

theorem proposition_3 (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ)
    (s F : ℝ) (hs : 0 < s) (hF : 0 < F) :
    (∀ Q qA qT : ℝ, IsEqTS θ s F Q qA qT → θ.r * F < s * qA →
      Q = demand θ (θ.c + θ.κ / θ.β) ∧ qA = Q ∧ qT = Q ∧ IsEqNA θ Q Q) ∧
    (θ.r * F < s * demand θ (θ.c + θ.κ / θ.β) →
      IsEqTS θ s F (demand θ (θ.c + θ.κ / θ.β))
        (demand θ (θ.c + θ.κ / θ.β))
        (demand θ (θ.c + θ.κ / θ.β))) := by sorry

end VaccineAMC.Framework
