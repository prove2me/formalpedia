-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_C_2
-- name    : SRAudit.TwoPhase.Supplement.proposition_C_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:28:06.095638+00:00
-- url     : https://prove2.me/theorems/1ed361c9-6249-4940-9f62-dbd0b1570b63
-- title:
--   Proposition C.2, OA-4 — the tier-1 game has a unique equilibrium for every input-price vector, and the inverse demand facing tier 2 is (C.5)
-- statement:
--   Fix a network $g$ with tier-1 firms $S(1)\subseteq\{a,b\}$, and the inverse demand $p^*_{(1)}$ of the buyer (Proposition C.1). In the tier-1 game $P_1$, firm $i\in S(1)$ chooses $q_i\in\mathbb R$ to maximize $(p^*_{(1)}(\sum_{i'\in S(1)}q_{i'})-v_1-p_{(2)i})q_i$. Assume $\beta>0$, $\alpha\ge v_T$, $g$ well formed.
--
--   1. For every vector of input prices $p_{(2)}=(p_{(2)i})_{i\in S(1)}$ the game $P_1$ has a unique pure-strategy equilibrium $q^*_{(1)}$.
--   2. The resulting inverse demand faced by the tier-2 suppliers of firm $i\in S(1)$ is
--   $$p^*_{(2)i}(q_{(1)})=\alpha-v_0-v_1-4\beta q_i-2\beta\sum_{i'\in S(1)\setminus\{i\}}q_{i'}.\qquad\text{(C.5)}$$
--
--   This is the second stage of the backward induction that proves Theorem 1.
--
--   **Formalization Note** Profiles and price vectors are indexed by both firms and normalised to $0$ at an absent firm.
--
--   Differences from the source:
--   - encoding: profiles q_(1) ∈ ∏_{i∈S(1)} C_i → functions Firm → ℝ vanishing outside S(1); reason: uniqueness is then meaningful; same instances
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-4, Proposition C.2, (C.5)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_C_2 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing)
    (g : Network ι) (hg : WellFormedNet g) :
    (∀ p2 : Firm → ℝ, ∃! q : Firm → ℝ, IsTier1Eq E g p2 q) ∧
    (∀ q : Firm → ℝ, (∀ x, x ∉ g.T1 → q x = 0) → ∀ i ∈ g.T1,
      invDemand2 E g q i = E.α - E.v0 - E.v1 - 4 * E.β * q i - 2 * E.β * ∑ i' ∈ g.T1.erase i, q i') := by sorry

end SRAudit.TwoPhase.Supplement
