-- Prove2me | Theorems.Thm_VidalHGS_Elitism_elite_biasedFitness_lt_one
-- name    : VidalHGS.Elitism.elite_biasedFitness_lt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:47.822355+00:00
-- url     : https://prove2.me/theorems/4ed19d77-731e-4488-afde-ed35a1349edd
-- title:
--   p. 17, Section 4.6, proof of the Proposition — an elite individual has BF < 1
-- statement:
--   Let $P$ be a subpopulation and $\mathit{nbElit} \in \mathbb{N}$ with $\mathit{nbElit} + 1 \le |P|$. Let $J \in P$ be among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness, i.e. fewer than $\mathit{nbElit}$ members of $P$ have strictly smaller cost than $J$. Then
--   $$BF_P(J) \le \frac{\mathit{nbElit} - 1}{|P| - 1} + 1 - \frac{\mathit{nbElit}}{|P| - 1} < 1.$$
--
--   This is the second sentence of the proof of the elitism Proposition: elite individuals lie strictly outside the removal zone $BF \ge 1$.
--
--   **Formalization Note.** All arithmetic is in $\mathbb{R}$. The hypotheses force $\mathit{nbElit} \ge 1$ and $|P| \ge 2$, so the denominator $|P| - 1$ is positive. The condition $\mathit{nbElit} \le |P| - 1$ is implicit in the paper (Table 1 gives $\mathit{nbElit} = el \times \mu \le \mu$, and the procedure acts on populations of more than $\mu$ individuals). The intermediate bound is kept in the paper's unsimplified form.
-- source:
--   Vidal, Crainic, Gendreau, Lahrichi and Rei, A Hybrid Genetic Algorithm for Multi-Depot and Periodic Vehicle Routing Problems, CIRRELT-2010-34 (July 2010), p. 17, Section 4.6, proof of the Proposition (second sentence)

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, p. 17, proof of the Proposition: an individual `J` among the `nbElit` best
in terms of fitness has
`BF(J) ≤ (nbElit − 1)/(nbIndiv − 1) + 1 − nbElit/(nbIndiv − 1) < 1`,
provided `nbElit ≤ nbIndiv − 1`. -/
theorem elite_biasedFitness_lt_one {α : Type*} [DecidableEq α]
    (c : α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (P : Finset α) (J : α)
    (hsize : nbElit + 1 ≤ P.card) (hJ : J ∈ P) (helite : IsElite c nbElit P J) :
    biasedFitness c Δ nbElit P J ≤
        ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) + 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) ∧
      biasedFitness c Δ nbElit P J < 1 := by sorry

end VidalHGS.Elitism
