-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_C_1
-- name    : SRAudit.TwoPhase.Supplement.proposition_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:26:53.341417+00:00
-- url     : https://prove2.me/theorems/ed64c723-8ba9-4577-9640-432da350248f
-- title:
--   Proposition C.1, OA-4 — the buyer's problem has a unique optimal quantity, and the inverse demand facing tier 1 is α − v0 − 2βqc
-- statement:
--   Consider the buyer's problem $P_0$ of §3.3: with inverse demand $p_{(0)}(q_c)=\alpha-\beta q_c$, unit cost $v_0$ and input price $p_{(1)}$, the buyer chooses $q_c\in\mathbb R$ to maximize $\pi_c(q_c)=(\alpha-\beta q_c-v_0-p_{(1)})q_c$. Assume $\beta>0$ and $\alpha\ge v_T$.
--
--   1. For every input price $p_{(1)}$ there is a unique optimal quantity $q^*_c$.
--   2. $q_c$ is optimal at $p_{(1)}$ exactly when $p_{(1)}=\alpha-v_0-2\beta q_c$; hence the inverse demand faced by the tier-1 firms is
--   $$p^*_{(1)}(q_c)=\alpha-v_0-2\beta q_c.\qquad\text{(C.1)}$$
--
--   This is the third stage of the backward induction that proves Theorem 1.
--
--   Differences from the source:
--   - reading: the resulting inverse demand function is (C.1) → q_c is optimal at p_(1) iff p_(1) = α − v0 − 2βq_c, and the defined inverse demand equals (C.1) at every q_c; reason: the inverse demand is the price at which q_c is optimal; the equivalence is what makes it a function
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-4, Proposition C.1, (C.1)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_C_1 (E : Demand) (hE : E.Standing) :
    (∀ p1 : ℝ, ∃! qc : ℝ, IsBuyerOptimal E p1 qc) ∧
    (∀ p1 qc : ℝ, IsBuyerOptimal E p1 qc ↔ p1 = E.α - E.v0 - 2 * E.β * qc) ∧
    (∀ qc : ℝ, invDemand1 E qc = E.α - E.v0 - 2 * E.β * qc) := by sorry

end SRAudit.TwoPhase.Supplement
