-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_2
-- name    : SRAudit.TwoPhase.Supplement.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:34:00.005708+00:00
-- url     : https://prove2.me/theorems/ab8a716a-872f-4648-abd5-0d22620441af
-- title:
--   Proposition 2, p. 16 (corrected: equal gains when ta ≥ 2tb + 2tab + 4) — a shared supplier raises q*c, m*c, π*c at least as much as a minority-exclusive one, which beats a majority-exclusive one
-- statement:
--   Let $\beta>0$ and $\alpha>v_T$. There is $M_0>0$ such that for every capacity $M\ge M_0$ and every well-formed network $g$ with $t_a\ge t_b$:
--
--   1. **(a)** Let $g_1$ add a shared supplier and $g_2$ a minority-exclusive supplier (to firm $b$). If $t_a<2t_b+2t_{ab}+4$, the increase of each of $q^*_c$, $m^*_c$, $\pi^*_c$ from $g$ to $g_1$ is strictly greater than from $g$ to $g_2$; if $t_a\ge2t_b+2t_{ab}+4$ the two increases are equal.
--   2. **(b)** Let $g_2$ add a minority-exclusive supplier and $g_3$ a majority-exclusive supplier (to firm $a$). The increase of each of $q^*_c$, $m^*_c$, $\pi^*_c$ from $g$ to $g_2$ is at least that from $g$ to $g_3$.
--
--   For the buyer a shared supplier is the most valuable, a majority-exclusive one the least; the proof of Theorem D.2 uses this ranking to obtain Assumption D.2 for the Cournot profit.
--
--   Differences from the source:
--   - reading: a production model with an (arbitrarily large) capacity M > 0 → ∃ M₀ > 0 such that the statement holds for every M ≥ M₀; reason: the closed forms of Proposition C.5, on which the proof rests, ignore the upper bound s ≤ M (OA-7–OA-8); they are the equilibrium once M exceeds every closed-form quantity, e.g. M₀ = (α − v_T)/β, uniformly over networks
--   - encoding: the majority tier-1 firm is indexed a (t_a ≥ t_b) → hypothesis |S_b| ≤ |S_a|; reason: the paper's labelling convention (pp. 15, OA-41); the case t_b > t_a is the same statement with a and b exchanged
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
--   - reading: adding a shared / minority-exclusive / majority-exclusive supplier to g → AddsShared, AddsExclusive b, AddsExclusive a; reason: the count representation (C.36)
--   - correction: (a) the increase from a shared supplier is strictly greater, for every g → strictly greater when t_a < 2t_b + 2t_ab + 4, equal when t_a ≥ 2t_b + 2t_ab + 4; reason: counterexample g = ⟨4,0,0⟩: by Proposition C.5 both ⟨4,0,1⟩ and ⟨4,1,0⟩ have q*_c = (α − v_T)/(4β); in that regime the added shared supplier sells nothing to a (Theorem 2(c), p. 16) and acts as an exclusive supplier of b; see DISPROOF.md
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), p. 16–17, Proposition 2; proof OA-10

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_2 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing)
    (hα : E.vT < E.α) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    ∀ g : Network ι, WellFormedNet g → g.Sb.card ≤ g.Sa.card →
    -- (a) shared vs minority-exclusive (corrected: strict unless `ta ≥ 2tb + 2tab + 4`)
    (∀ (g₁ g₂ : Network ι) (j₁ j₂ : ι), AddsShared g g₁ j₁ → AddsExclusive .b g g₂ j₂ →
      ((g.Sa.card : ℝ) < 2 * g.Sb.card + 2 * g.Sab.card + 4 →
        qcStar E M g₂ - qcStar E M g < qcStar E M g₁ - qcStar E M g ∧
        mcStar E M g₂ - mcStar E M g < mcStar E M g₁ - mcStar E M g ∧
        picStar E M g₂ - picStar E M g < picStar E M g₁ - picStar E M g) ∧
      (2 * (g.Sb.card : ℝ) + 2 * g.Sab.card + 4 ≤ g.Sa.card →
        qcStar E M g₂ - qcStar E M g = qcStar E M g₁ - qcStar E M g ∧
        mcStar E M g₂ - mcStar E M g = mcStar E M g₁ - mcStar E M g ∧
        picStar E M g₂ - picStar E M g = picStar E M g₁ - picStar E M g)) ∧
    -- (b) minority-exclusive vs majority-exclusive
    (∀ (g₂ g₃ : Network ι) (j₂ j₃ : ι), AddsExclusive .b g g₂ j₂ → AddsExclusive .a g g₃ j₃ →
      qcStar E M g₃ - qcStar E M g ≤ qcStar E M g₂ - qcStar E M g ∧
      mcStar E M g₃ - mcStar E M g ≤ mcStar E M g₂ - mcStar E M g ∧
      picStar E M g₃ - picStar E M g ≤ picStar E M g₂ - picStar E M g) := by sorry

end SRAudit.TwoPhase.Supplement
