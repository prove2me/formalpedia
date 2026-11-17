-- Prove2me | Theorems.Thm_QuantumLTF_Majority_sum_by_intersectionIndex
-- name    : QuantumLTF.Majority.sum_by_intersectionIndex
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:49:59.326003+00:00
-- url     : https://prove2.me/theorems/aac8e21e-7985-4d17-a850-88c6216b405d
-- title:
--   Sum over the Boolean cube grouped by intersection size
-- statement:
--   For a fixed support $A$ of size $r$, any sum over Boolean strings of a function depending only on $|A\cap S|$ can be grouped by intersection size:
--
--   $$
--   \sum_{S\subseteq[n]}f(|A\cap S|)=2^{n-r}\sum_{a=0}^r{r\choose a}f(a).
--   $$
--
--   This is the weighted-sum form of the intersection-fiber cardinality formula.
-- source:
--   Immediate fiberwise summation consequence of Boolean-cube intersection counting; used in Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem sum_by_intersectionIndex : ∀ n r : ℕ, r ≤ n → ∀ A : ExactSupports n r, ∀ f : Fin (r+1) → ℝ, ∑ S : Qubits n, f (intersectionIndex A S) = (2^(n-r) : ℝ) * ∑ a : Fin (r+1), (r.choose a : ℝ) * f a := by sorry

end QuantumLTF.Majority
