-- Prove2me | Theorems.Thm_UnitCapMCF_Excess_lemma5_small_band_cube
-- name    : UnitCapMCF.Excess.lemma5_small_band_cube
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:32:22.062674+00:00
-- url     : https://prove2.me/theorems/25bcaef6-0364-4bb1-9d98-6cdcb1bb9542
-- title:
--   Proof of Lemma 5, p. 410 — a vertex band and its arc band are small
-- statement:
--   In a unit-capacity network with $n$ vertices, let $N_i$ be the vertices with levels $6i,6i-1,\ldots,6i-5$, and let $A_{2i}$ be the associated arc band. If $\lambda>0$ is an integer divisible by six and $\lambda=n^{2/3}$, then some $i$ with $1\le i\le\lambda/6$ satisfies both
--
--   $$|N_i|\le\frac{n}{\lambda/6}=6n^{1/3},\qquad |A_{2i}|\le36n^{2/3}.$$
--
--   This is the counting step for the second case of Lemma 5.
--
--   **Formalization Note** The positive-$\lambda$ pin makes the range nonempty. The paper's sixth-divisibility simplification is explicit. $n^{1/3}$ and $n^{2/3}$ are real powers.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), p. 410, proof of Lemma 5, third paragraph and footnote 6; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

namespace UnitCapMCF.Excess

/-- Goldberg et al., STACS 2015, proof of Lemma 5, p. 410, third paragraph. -/
theorem lemma5_small_band_cube {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (hN : IsUnitCapacity N)
    (ε : ℝ) (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (lam : ℕ) (hlampos : 0 < lam) (h6 : 6 ∣ lam)
    (hlam : (lam : ℝ) = (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3)) :
    ∃ i : ℕ, 1 ≤ i ∧ 6 * i ≤ lam ∧
      ((bandVerts ε p' p i).card : ℝ) ≤
        6 * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3) ∧
      ((bandArcs N f' f ε p' p (2 * i)).card : ℝ) ≤
        36 * (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) := by sorry

end UnitCapMCF.Excess
