-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_C_4
-- name    : SRAudit.TwoPhase.Supplement.proposition_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:31:39.863674+00:00
-- url     : https://prove2.me/theorems/12914968-c6bd-4f7a-a0dc-9468977c90a0
-- title:
--   Proposition C.4, OA-7 — in equilibrium the buyer's profit is β(q*c)²
-- statement:
--   Let $g$ be a well-formed non-null network, $\beta>0$, $\alpha\ge v_T$, $M>0$. In every production phase equilibrium of $g$ the buyer's profit is
--   $$\pi^*_c=(p^*_{(0)}-v_0-p^*_{(1)})q^*_c=\beta\,(q^*_c)^2.$$
--   The buyer's profit therefore moves with its quantity, which the proof of Theorem 2 uses.
--
--   Differences from the source:
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-7, Proposition C.4

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_C_4 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) (M : ℝ)
    (hM : 0 < M) (g : Network ι) (hg : WellFormedNet g) (hnull : ¬ IsNullNet g)
    (e : ProdOutcome ι) (he : IsProdEq E g M e) :
    buyerProfit E e.p1 e.qc = E.β * e.qc ^ 2 := by sorry

end SRAudit.TwoPhase.Supplement
