-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_2
-- name    : SRAudit.TwoPhase.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:32:47.533053+00:00
-- url     : https://prove2.me/theorems/44c20fe2-05dc-4b84-a656-67ff6bf79c57
-- title:
--   Theorem 2, p. 15 (corrected: weak signs at boundary networks) — comparative statics of Table 1 when a tier-2 supplier is added
-- statement:
--   Let $\beta>0$ and $\alpha>v_T$. There is $M_0>0$ such that for every capacity $M\ge M_0$ the following holds for every well-formed network $g$ with $t_a=|S_a|\ge t_b=|S_b|$ ($a$ is the majority tier-1 firm), $t_{ab}=|S_{ab}|$, and every network $g'$ obtained by adding one fresh tier-2 supplier. Write $\Delta f=f(g')-f(g)$ for the equilibrium variables of Table 1.
--
--   **(a) Majority-exclusive supplier (column I).** $\Delta q^*_c,\Delta\pi^*_c>0$; if $g$ is non-null: $\Delta m^*_c>0$, $\Delta p^*_{(1)}<0$, $\Delta q^*_a,\Delta m^*_a,\Delta\pi^*_a>0$, $\Delta p^*_{(2)a}<0$, $\Delta\rho^*_a\ge0$; and if firm $b$ is present: $\Delta\rho^*_a>0$, $\Delta p^*_{(2)b}<0$, $\Delta\rho^*_b<0$, $\Delta q^*_b,\Delta m^*_b,\Delta\pi^*_b\le0$, strictly $<0$ when $t_b>0$ or $t_a\ge2t_b+2t_{ab}+2$.
--
--   **(b) Minority-exclusive supplier (column II).** $\Delta q^*_c,\Delta\pi^*_c>0$; if $g$ is non-null: $\Delta m^*_c>0$, $\Delta p^*_{(1)}<0$, $\Delta q^*_a,\Delta m^*_a,\Delta\pi^*_a\le0$ (strictly $<0$ when $t_a>0$), $\Delta p^*_{(2)a}<0$, $\Delta\rho^*_a<0$; and if $b$ is present: $\Delta q^*_b,\Delta m^*_b,\Delta\pi^*_b>0$, $\Delta p^*_{(2)b}<0$, $\Delta\rho^*_b>0$.
--
--   **(c) Shared supplier.** If $t_a\le2t_b+2t_{ab}+2$ (column III): $\Delta q^*_c,\Delta\pi^*_c>0$; if $g$ is non-null: $\Delta m^*_c>0$, $\Delta p^*_{(1)}<0$, $\Delta p^*_{(2)a}<0$, $\Delta\rho^*_a\le0$ (strictly when $t_a\ne t_b$); if $b$ is present: $\Delta q^*_b,\Delta m^*_b,\Delta\pi^*_b>0$, $\Delta p^*_{(2)b}<0$, $\Delta\rho^*_b\ge0$ (strictly when $t_a\ne t_b$). If $t_a>2t_b+2t_{ab}+2$, all the strict signs of column II hold. In column III the effect on $q^*_a,m^*_a,\pi^*_a$ is "+/−": there are networks (with $t_a\le2t_b+2t_{ab}+2$) where adding a shared supplier increases all three, and networks where it decreases all three.
--
--   The buyer's gain from every added supplier is what makes dropping a supplier costly in the auditing phase.
--
--   **Formalization Note** Firm-level variables are claimed for a non-null $g$ and, for firm $b$, when $b$ is present in $g$; $q^*_c$ and $\pi^*_c$ for every $g$ (Appendix C.3). The "+/−" instances are stated on networks labelled by $\mathbb N$.
--
--   Differences from the source:
--   - reading: a production model with an (arbitrarily large) capacity M > 0 → ∃ M₀ > 0 such that the statement holds for every M ≥ M₀; reason: the closed forms of Proposition C.5, on which the proof rests, ignore the upper bound s ≤ M (OA-7–OA-8); they are the equilibrium once M exceeds every closed-form quantity, e.g. M₀ = (α − v_T)/β, uniformly over networks
--   - encoding: the majority tier-1 firm is indexed a (t_a ≥ t_b) → hypothesis |S_b| ≤ |S_a|; reason: the paper's labelling convention (pp. 15, OA-41); the case t_b > t_a is the same statement with a and b exchanged
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
--   - reading: adding a tier-2 supplier to g → g′ with a fresh label j added to S_a, S_b (exclusive, the firm joins if absent) or S_ab (both firms then present); reason: the count representation (C.36) and the finite differences Δ1, Δ2, Δ3 of OA-9
--   - reading: all comparative statics other than q*_c, π*_c apply to non-null networks → firm-level claims for non-null g; firm-b claims when b ∈ S(1) of g; reason: Appendix C.3 (OA-9); an absent firm has no quantity, margin, price or share
--   - correction: Table 1 column I: q*_b, m*_b, π*_b strictly −; ρ*_a strictly + → ≤ 0, strict when t_b > 0 or t_a ≥ 2t_b + 2t_ab + 2; ρ*_a ≥ 0, strict when b is present; reason: the proof's own (C.43) is 0 at t_b = 0 and (C.46) is '> 0 if t_b + t_ab > 0'; e.g. g = ⟨0,0,1⟩ → ⟨1,0,1⟩ leaves q*_b unchanged; exact rational evaluation of Proposition C.5 for all t_a,t_b,t_ab < 20 finds zero differences exactly at these networks
--   - correction: Table 1 column II: q*_a, m*_a, π*_a strictly − → ≤ 0, strict when t_a > 0; reason: with t_a = t_b = 0 (only shared suppliers), adding an exclusive supplier of b leaves q*_a unchanged by Proposition C.5 (exact evaluation, e.g. ⟨0,0,1⟩ → ⟨0,1,1⟩)
--   - correction: Table 1 column III: ρ*_a strictly −, ρ*_b strictly + → weak, strict when t_a ≠ t_b; reason: when t_a = t_b the network stays symmetric after adding a shared supplier and both shares remain 1/2 (Proposition C.5)
--   - reading: '+/−': there exist instances of increase and of decrease → two existential claims over networks labelled by ℕ with t_a ≤ 2t_b + 2t_ab + 2; reason: Table 1 caption; Proposition C.6 locates the threshold
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), p. 15, Theorem 2 and Table 1; proof OA-9–OA-10, (C.37)–(C.46)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_2 {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) (hα : E.vT < E.α) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    -- (a) adding a majority-exclusive supplier: column (I)
    (∀ (g g' : Network ι) (j : ι), WellFormedNet g → g.Sb.card ≤ g.Sa.card →
      AddsExclusive .a g g' j →
      qcStar E M g < qcStar E M g' ∧ picStar E M g < picStar E M g' ∧
      (¬ IsNullNet g →
        mcStar E M g < mcStar E M g' ∧ p1Star E M g' < p1Star E M g ∧
        qStar E M g .a < qStar E M g' .a ∧ mStar E M g .a < mStar E M g' .a ∧
        piStar E M g .a < piStar E M g' .a ∧ p2Star E M g' .a < p2Star E M g .a ∧
        rhoStar E M g .a ≤ rhoStar E M g' .a ∧
        (Firm.b ∈ g.T1 →
          rhoStar E M g .a < rhoStar E M g' .a ∧
          qStar E M g' .b ≤ qStar E M g .b ∧ mStar E M g' .b ≤ mStar E M g .b ∧
          piStar E M g' .b ≤ piStar E M g .b ∧
          (0 < g.Sb.card ∨ 2 * (g.Sb.card : ℝ) + 2 * g.Sab.card + 2 ≤ g.Sa.card →
            qStar E M g' .b < qStar E M g .b ∧ mStar E M g' .b < mStar E M g .b ∧
            piStar E M g' .b < piStar E M g .b) ∧
          p2Star E M g' .b < p2Star E M g .b ∧ rhoStar E M g' .b < rhoStar E M g .b))) ∧
    -- (b) adding a minority-exclusive supplier: column (II)
    (∀ (g g' : Network ι) (j : ι), WellFormedNet g → g.Sb.card ≤ g.Sa.card →
      AddsExclusive .b g g' j →
      qcStar E M g < qcStar E M g' ∧ picStar E M g < picStar E M g' ∧
      (¬ IsNullNet g →
        mcStar E M g < mcStar E M g' ∧ p1Star E M g' < p1Star E M g ∧
        qStar E M g' .a ≤ qStar E M g .a ∧ mStar E M g' .a ≤ mStar E M g .a ∧
        piStar E M g' .a ≤ piStar E M g .a ∧
        (0 < g.Sa.card →
          qStar E M g' .a < qStar E M g .a ∧ mStar E M g' .a < mStar E M g .a ∧
          piStar E M g' .a < piStar E M g .a) ∧
        p2Star E M g' .a < p2Star E M g .a ∧ rhoStar E M g' .a < rhoStar E M g .a ∧
        (Firm.b ∈ g.T1 →
          qStar E M g .b < qStar E M g' .b ∧ mStar E M g .b < mStar E M g' .b ∧
          piStar E M g .b < piStar E M g' .b ∧ p2Star E M g' .b < p2Star E M g .b ∧
          rhoStar E M g .b < rhoStar E M g' .b))) ∧
    -- (c) adding a shared supplier: column (III) if `ta ≤ 2tb + 2tab + 2`, column (II) otherwise
    (∀ (g g' : Network ι) (j : ι), WellFormedNet g → g.Sb.card ≤ g.Sa.card →
      AddsShared g g' j →
      ((g.Sa.card : ℝ) ≤ 2 * g.Sb.card + 2 * g.Sab.card + 2 →
        qcStar E M g < qcStar E M g' ∧ picStar E M g < picStar E M g' ∧
        (¬ IsNullNet g →
          mcStar E M g < mcStar E M g' ∧ p1Star E M g' < p1Star E M g ∧
          p2Star E M g' .a < p2Star E M g .a ∧ rhoStar E M g' .a ≤ rhoStar E M g .a ∧
          (g.Sa.card ≠ g.Sb.card → rhoStar E M g' .a < rhoStar E M g .a) ∧
          (Firm.b ∈ g.T1 →
            qStar E M g .b < qStar E M g' .b ∧ mStar E M g .b < mStar E M g' .b ∧
            piStar E M g .b < piStar E M g' .b ∧ p2Star E M g' .b < p2Star E M g .b ∧
            rhoStar E M g .b ≤ rhoStar E M g' .b ∧
            (g.Sa.card ≠ g.Sb.card → rhoStar E M g .b < rhoStar E M g' .b)))) ∧
      (2 * (g.Sb.card : ℝ) + 2 * g.Sab.card + 2 < g.Sa.card →
        qcStar E M g < qcStar E M g' ∧ picStar E M g < picStar E M g' ∧
        mcStar E M g < mcStar E M g' ∧ p1Star E M g' < p1Star E M g ∧
        qStar E M g' .a < qStar E M g .a ∧ mStar E M g' .a < mStar E M g .a ∧
        piStar E M g' .a < piStar E M g .a ∧
        p2Star E M g' .a < p2Star E M g .a ∧ rhoStar E M g' .a < rhoStar E M g .a ∧
        (Firm.b ∈ g.T1 →
          qStar E M g .b < qStar E M g' .b ∧ mStar E M g .b < mStar E M g' .b ∧
          piStar E M g .b < piStar E M g' .b ∧ p2Star E M g' .b < p2Star E M g .b ∧
          rhoStar E M g .b < rhoStar E M g' .b))) ∧
    -- column (III), firm a: "+/−", both an increase and a decrease occur
    (∃ (g g' : Network ℕ) (j : ℕ), WellFormedNet g ∧ ¬ IsNullNet g ∧ g.Sb.card ≤ g.Sa.card ∧
      (g.Sa.card : ℝ) ≤ 2 * g.Sb.card + 2 * g.Sab.card + 2 ∧ AddsShared g g' j ∧
      qStar E M g .a < qStar E M g' .a ∧ mStar E M g .a < mStar E M g' .a ∧
      piStar E M g .a < piStar E M g' .a) ∧
    (∃ (g g' : Network ℕ) (j : ℕ), WellFormedNet g ∧ ¬ IsNullNet g ∧ g.Sb.card ≤ g.Sa.card ∧
      (g.Sa.card : ℝ) ≤ 2 * g.Sb.card + 2 * g.Sab.card + 2 ∧ AddsShared g g' j ∧
      qStar E M g' .a < qStar E M g .a ∧ mStar E M g' .a < mStar E M g .a ∧
      piStar E M g' .a < piStar E M g .a) := by sorry

end SRAudit.TwoPhase.Supplement
