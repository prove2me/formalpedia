-- Prove2me | Theorems.Thm_UnitCapMCF_Excess_lemma5_small_band_sqrt
-- name    : UnitCapMCF.Excess.lemma5_small_band_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:47.849518+00:00
-- url     : https://prove2.me/theorems/254ae8b8-e01a-4a75-97c3-4f8446f562f7
-- title:
--   Proof of Lemma 5, p. 410 — a band has at most 3√m arcs
-- statement:
--   In a unit-capacity network with $m$ input arcs, let $f'$ and $f$ be the entry and current pseudoflows, and let the arc bands $A_i$ be determined by their price levels. If $\lambda>0$ is an integer divisible by three and $\lambda=\sqrt m$, then some $i$ with $1\le i\le\lambda/3$ satisfies
--
--   $$|A_i|\le\frac{m}{\lambda/3}=3\sqrt m.$$
--
--   The small band gives a cut of the size needed for the first case of Lemma 5.
--
--   **Formalization Note** The positive-$\lambda$ pin makes the index range nonempty; the zero-arc case of the goal does not need a band. The $2\varepsilon$ and $\varepsilon$ optimality assumptions carry the pseudoflow constraints of the cost-scale state. The count $m$ excludes reverse arcs.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), p. 410, proof of Lemma 5, second paragraph and footnote 5; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

namespace UnitCapMCF.Excess

/-- Goldberg et al., STACS 2015, proof of Lemma 5, p. 410, second paragraph. -/
theorem lemma5_small_band_sqrt {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (hN : IsUnitCapacity N)
    (ε : ℝ) (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (lam : ℕ) (hlampos : 0 < lam) (h3 : 3 ∣ lam)
    (hlam : (lam : ℝ) = Real.sqrt (numArcs N : ℝ)) :
    ∃ i : ℕ, 1 ≤ i ∧ 3 * i ≤ lam ∧
      ((bandArcs N f' f ε p' p i).card : ℝ) ≤
        3 * Real.sqrt (numArcs N : ℝ) := by sorry

end UnitCapMCF.Excess
