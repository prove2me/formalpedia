-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_lemma_A_4
-- name    : SimpleCorrMFG.Conv.lemma_A_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:30.650069+00:00
-- url     : https://prove2.me/theorems/ffcb911d-5ec9-495a-af68-b23478732449
-- title:
--   Lemma A.4, p. 30 — a regular conditional distribution given $\mathcal C$ and given $\tilde{\mathcal C}\supseteq\mathcal C$ is one given every $\mathcal G$ in between
-- statement:
--   Let $\mathcal Y$ be a Polish space, $Y$ a $\mathcal Y$-valued and $\kappa$ a $\mathcal P(\mathcal Y)$-valued random variable on $(\Omega,\mathcal F,P)$, and $\mathcal C,\mathcal G,\tilde{\mathcal C}$ sub-σ-algebras of $\mathcal F$ with
--   $$\mathcal C\subseteq\mathcal G\subseteq\tilde{\mathcal C}.$$
--   If $\kappa$ is a regular conditional distribution of $Y$ given $\mathcal C$ as well as given $\tilde{\mathcal C}$, then $\kappa$ is also a regular conditional distribution of $Y$ given $\mathcal G$.
--
--   In Step Four of the proof of Theorem 6.1 it moves the conditional law of player 1's state from the σ-algebra of the empirical measure of trajectories down to that of the empirical flow.
--
--   **Formalization Note** $\kappa$ takes values in Mathlib's `ProbabilityMeasure` with its Giry σ-algebra.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 30, Lemma A.4 (with the standing assumptions of Appendix A, p. 27)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_RegCondDistrib

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Lemma A.4 (p. 30). -/
theorem lemma_A_4 {Ω 𝒴 : Type*} (C G C' : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → 𝒴) (κ : Ω → ProbabilityMeasure 𝒴) (hY : Measurable Y) (hκ : Measurable κ)
    (hCG : C ≤ G) (hGC' : G ≤ C') (hC' : C' ≤ mΩ)
    (hC : IsRegCondDistrib P Y (fun ω => (κ ω : Measure 𝒴)) C)
    (hC'rcd : IsRegCondDistrib P Y (fun ω => (κ ω : Measure 𝒴)) C') :
    IsRegCondDistrib P Y (fun ω => (κ ω : Measure 𝒴)) G := by sorry

end SimpleCorrMFG.Conv
