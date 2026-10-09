-- Prove2me | Theorems.Thm_UnitCapMCF_Excess_lemma5_second_phase_excess
-- name    : UnitCapMCF.Excess.lemma5_second_phase_excess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:33:21.961675+00:00
-- url     : https://prove2.me/theorems/b446e10d-2413-4881-96d7-c0f9228456e4
-- title:
--   Lemma 5, p. 410 — second-phase excess is at most 3λ or 36λ
-- statement:
--   Consider a unit-capacity network with $m$ input arcs and $n$ vertices. At a current cost scale $\varepsilon>0$, let $f'$ be an entry circulation that is $2\varepsilon$-optimal at prices $p'$, and let $f$ be the current $\varepsilon$-optimal pseudoflow at prices $p$. Write $d(v)=(p(v)-p'(v))/\varepsilon$ and $\lambda=\min\{\sqrt m,n^{2/3}\}$. Suppose $\lambda$ is a natural number divisible by three, all levels $d(v)$ are integers, every excess has level at least $\lambda$, and every deficit has level zero. When the corresponding case occurs,
--
--   $$\lambda=\sqrt m\Longrightarrow \sum_{v:e_f(v)>0}e_f(v)\le3\lambda,$$
--
--   $$\lambda=n^{2/3}\text{ and }6\mid\lambda\Longrightarrow \sum_{v:e_f(v)>0}e_f(v)\le36\lambda.$$
--
--   This makes the paper's $O(\lambda)$ second-phase excess claim explicit in its two cases. It supplies the excess bound used in the running-time analysis; that running-time theorem is outside this mission.
--
--   **Formalization Note** The current cost-scale invariants are hypotheses, including integral levels and zero level at deficits. Divisibility by three is the simplification of footnote 5; divisibility by six is used only in the second case, as in footnote 6. Costs and flows are real, and $m$ counts one input arc per reverse pair.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), p. 410, Lemma 5 and proof, footnotes 5–6; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

namespace UnitCapMCF.Excess

/-- Goldberg et al., STACS 2015, Lemma 5 and its proof, p. 410. -/
theorem lemma5_second_phase_excess {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (hN : IsUnitCapacity N)
    (ε : ℝ) (hε : 0 < ε) (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f')
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (hd : ∀ v, ∃ k : ℤ, dlevel ε p' p v = k)
    (lam : ℕ)
    (hlam : (lam : ℝ) = min (Real.sqrt (numArcs N : ℝ))
      ((Fintype.card V : ℝ) ^ ((2 : ℝ) / 3)))
    (h3 : 3 ∣ lam)
    (hexc : ∀ v, 0 < CostScaling.Refine.excess N f v →
      (lam : ℝ) ≤ dlevel ε p' p v)
    (hdef : ∀ v, CostScaling.Refine.excess N f v < 0 →
      dlevel ε p' p v = 0) :
    ((lam : ℝ) = Real.sqrt (numArcs N : ℝ) →
      totalExcess N f ≤ 3 * (lam : ℝ)) ∧
    ((lam : ℝ) = (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) →
      6 ∣ lam → totalExcess N f ≤ 36 * (lam : ℝ)) := by sorry

end UnitCapMCF.Excess
