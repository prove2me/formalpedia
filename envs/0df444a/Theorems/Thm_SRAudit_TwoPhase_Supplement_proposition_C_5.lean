-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_C_5
-- name    : SRAudit.TwoPhase.Supplement.proposition_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:32:16.709205+00:00
-- url     : https://prove2.me/theorems/fc1ec79a-5f7d-4d63-bfeb-12dd08412230
-- title:
--   Proposition C.5, OA-7 — closed-form equilibrium quantities in the regimes ta ≤ 2tb + 2tab + 2 and ta ≥ 2tb + 2tab + 2
-- statement:
--   Let $\beta>0$, $\alpha\ge v_T$. There is a capacity threshold $M_0>0$ such that for every $M\ge M_0$ the following holds. Let $g$ be a well-formed non-null network with $t_a=|S_a|\ge t_b=|S_b|$, $t_{ab}=|S_{ab}|$, and $-i$ the other tier-1 firm. In its production phase equilibrium:
--
--   **(a)** if $t_a\le2t_b+2t_{ab}+2$:
--   1. each $j\in S_i$, $i\in S(1)$, supplies $s^*_{j,i}=s_e(t_i,t_{-i},t_{ab})$;
--   2. each $j\in S_{ab}$ supplies $s^*_{j,a}=s_s(t_a,t_b,t_{ab})$ and $s^*_{j,b}=s_s(t_b,t_a,t_{ab})$;
--   3. each $i\in S(1)$ supplies $q^*_i=t_is_e(t_i,t_{-i},t_{ab})+t_{ab}s_s(t_i,t_{-i},t_{ab})=q_{(1)}(t_i,t_{-i},t_{ab})$;
--   4. $q^*_c=t_as_e(t_a,t_b,t_{ab})+t_bs_e(t_b,t_a,t_{ab})+t_{ab}(s_s(t_a,t_b,t_{ab})+s_s(t_b,t_a,t_{ab}))=q(t_a,t_b,t_{ab})$ (C.26);
--
--   **(b)** if $t_a\ge2t_b+2t_{ab}+2$:
--   1. each $j\in S_a$ supplies $s^*_{j,a}=s_e(t_a,t_b+t_{ab},0)$, each $j\in S_b$ supplies $s^*_{j,b}=s_e(t_b+t_{ab},t_a,0)$;
--   2. each $j\in S_{ab}$ supplies $s^*_{j,a}=0$ and $s^*_{j,b}=s_e(t_b+t_{ab},t_a,0)$;
--   3. $q^*_a=t_as_e(t_a,t_b+t_{ab},0)=q_{(1)}(t_a,t_b+t_{ab},0)$ and $q^*_b=(t_b+t_{ab})s_e(t_b+t_{ab},t_a,0)=q_{(1)}(t_b+t_{ab},t_a,0)$;
--   4. $q^*_c=t_as_e(t_a,t_b+t_{ab},0)+(t_b+t_{ab})s_e(t_b+t_{ab},t_a,0)=q(t_a,t_b+t_{ab},0)$ (C.27).
--
--   Here $L,s_e,s_s,q_{(1)},q$ are (C.21)–(C.25). Every comparative-statics result of the paper is computed from these formulas.
--
--   Differences from the source:
--   - reading: a production model with an (arbitrarily large) capacity M > 0 → ∃ M₀ > 0 such that the statement holds for every M ≥ M₀; reason: the closed forms of Proposition C.5, on which the proof rests, ignore the upper bound s ≤ M (OA-7–OA-8); they are the equilibrium once M exceeds every closed-form quantity, e.g. M₀ = (α − v_T)/β, uniformly over networks
--   - encoding: the majority tier-1 firm is indexed a (t_a ≥ t_b) → hypothesis |S_b| ≤ |S_a|; reason: the paper's labelling convention (pp. 15, OA-41); the case t_b > t_a is the same statement with a and b exchanged
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
--   - reading: firm i chooses q*_i (i ∈ S(1)) in case (b) → the formulas for q*_a and q*_b are claimed when the firm is present; reason: an absent firm has no quantity; when b is absent its formula is 0 anyway
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-7, Proposition C.5, (C.21)–(C.27)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_C_5 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    ∀ g : Network ι, WellFormedNet g → ¬ IsNullNet g → g.Sb.card ≤ g.Sa.card →
    ∀ e : ProdOutcome ι, IsProdEq E g M e →
    -- (a) the case `ta ≤ 2tb + 2tab + 2`
    ((g.Sa.card : ℝ) ≤ 2 * g.Sb.card + 2 * g.Sab.card + 2 →
      (∀ i ∈ g.T1, ∀ j ∈ g.excl i,
        e.s2 j i = se E (g.excl i).card (g.excl (otherFirm i)).card g.Sab.card) ∧
      (∀ j ∈ g.Sab, e.s2 j .a = ss E g.Sa.card g.Sb.card g.Sab.card ∧
        e.s2 j .b = ss E g.Sb.card g.Sa.card g.Sab.card) ∧
      (∀ i ∈ g.T1,
        e.q1 i = (g.excl i).card * se E (g.excl i).card (g.excl (otherFirm i)).card g.Sab.card +
          g.Sab.card * ss E (g.excl i).card (g.excl (otherFirm i)).card g.Sab.card ∧
        e.q1 i = q1f E (g.excl i).card (g.excl (otherFirm i)).card g.Sab.card) ∧
      (e.qc = g.Sa.card * se E g.Sa.card g.Sb.card g.Sab.card +
          g.Sb.card * se E g.Sb.card g.Sa.card g.Sab.card +
          g.Sab.card * (ss E g.Sa.card g.Sb.card g.Sab.card + ss E g.Sb.card g.Sa.card g.Sab.card) ∧
        e.qc = qf E g.Sa.card g.Sb.card g.Sab.card)) ∧
    -- (b) the case `ta ≥ 2tb + 2tab + 2`
    (2 * (g.Sb.card : ℝ) + 2 * g.Sab.card + 2 ≤ g.Sa.card →
      (∀ j ∈ g.Sa, e.s2 j .a = se E g.Sa.card (g.Sb.card + g.Sab.card) 0) ∧
      (∀ j ∈ g.Sb, e.s2 j .b = se E (g.Sb.card + g.Sab.card) g.Sa.card 0) ∧
      (∀ j ∈ g.Sab, e.s2 j .a = 0 ∧ e.s2 j .b = se E (g.Sb.card + g.Sab.card) g.Sa.card 0) ∧
      (Firm.a ∈ g.T1 →
        e.q1 .a = g.Sa.card * se E g.Sa.card (g.Sb.card + g.Sab.card) 0 ∧
        e.q1 .a = q1f E g.Sa.card (g.Sb.card + g.Sab.card) 0) ∧
      (Firm.b ∈ g.T1 →
        e.q1 .b = (g.Sb.card + g.Sab.card) * se E (g.Sb.card + g.Sab.card) g.Sa.card 0 ∧
        e.q1 .b = q1f E (g.Sb.card + g.Sab.card) g.Sa.card 0) ∧
      (e.qc = g.Sa.card * se E g.Sa.card (g.Sb.card + g.Sab.card) 0 +
          (g.Sb.card + g.Sab.card) * se E (g.Sb.card + g.Sab.card) g.Sa.card 0 ∧
        e.qc = qf E g.Sa.card (g.Sb.card + g.Sab.card) 0)) := by sorry

end SRAudit.TwoPhase.Supplement
