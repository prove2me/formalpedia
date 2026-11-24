-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_1
-- name    : SRAudit.TwoPhase.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:31:00.271389+00:00
-- url     : https://prove2.me/theorems/a62e9510-606a-458e-b0f8-d8875a0afda4
-- title:
--   Theorem 1, p. 15 — every non-null supply network has a unique production phase equilibrium, for every capacity M > 0
-- statement:
--   Let $g$ be a well-formed supply network that is not the null network, let $\beta>0$, $\alpha\ge v_T$, and let $M>0$ be the tier-2 capacity. Then there is exactly one production phase equilibrium
--   $$(p^*_{(0)},p^*_{(1)},p^*_{(2)},q^*_c,q^*_{(1)},s^*_{(2)})$$
--   in $g$: a tier-2 equilibrium $s^*_{(2)}$ of $P_2$ with the resulting prices $p^*_{(2)}$, a tier-1 equilibrium $q^*_{(1)}$ of $P_1$ given $p^*_{(2)}$ with the resulting price $p^*_{(1)}$, and the buyer's optimal quantity $q^*_c$ given $p^*_{(1)}$ with the selling price $p^*_{(0)}=\alpha-\beta q^*_c$.
--
--   The buyer's production profit $\pi(\gamma)$ in the auditing phase is its profit in this equilibrium.
--
--   Differences from the source:
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
--   - encoding: tuples (p*_(0), p*_(1), p*_(2), q*_c, q*_(1), s*_(2)) over the firms present → total functions normalised to 0 at absent firms and off supply links; reason: uniqueness is then meaningful; same instances
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), p. 15, Theorem 1 (production phase equilibrium, p. 14)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_1 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) (M : ℝ) (hM : 0 < M)
    (g : Network ι) (hg : WellFormedNet g) (hnull : ¬ IsNullNet g) :
    ∃! e : ProdOutcome ι, IsProdEq E g M e := by sorry

end SRAudit.TwoPhase.Supplement
