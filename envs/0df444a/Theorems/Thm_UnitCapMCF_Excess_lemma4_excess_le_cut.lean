-- Prove2me | Theorems.Thm_UnitCapMCF_Excess_lemma4_excess_le_cut
-- name    : UnitCapMCF.Excess.lemma4_excess_le_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:35.647991+00:00
-- url     : https://prove2.me/theorems/210762bd-6be9-4987-9bb8-cb86b14de624
-- title:
--   Lemma 4, p. 410 — an excess–deficit cut bounds total excess
-- statement:
--   Let $f'$ be a circulation and $f$ a pseudoflow in a finite network. Let $Y\subseteq E^+$ meet every path in $G^+$ from a vertex with positive excess under $f$ to a vertex with negative excess. Then
--
--   $$\sum_{v:e_f(v)>0}e_f(v)\le\sum_{(v,w)\in Y}\bigl(f'(v,w)-f(v,w)\bigr)\le\sum_{(v,w)\in Y}u_f(v,w).$$
--
--   The result turns any such cut into a quantitative bound on the excess left in the pseudoflow.
--
--   **Formalization Note** The cut is required to lie inside $E^+$; allowing arbitrary arcs of $E$ makes the first inequality false. Reachability expresses the paper's path condition.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), p. 410, Lemma 4; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

namespace UnitCapMCF.Excess

/-- Goldberg et al., STACS 2015, Lemma 4, p. 410. -/
theorem lemma4_excess_le_cut {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (f' f : V → V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f')
    (hf : CostScaling.Refine.IsPseudoflow N f)
    (Y : Finset (V × V)) (hY : IsExcessDeficitCut N f' f Y) :
    totalExcess N f ≤ ∑ a ∈ Y, (f' a.1 a.2 - f a.1 a.2) ∧
    (∑ a ∈ Y, (f' a.1 a.2 - f a.1 a.2)) ≤
      ∑ a ∈ Y, CycleCanceling.MinMean.resCap N f a.1 a.2 := by sorry

end UnitCapMCF.Excess
