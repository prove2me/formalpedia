-- Prove2me | Theorems.Thm_VapnikChervonenkis_GrowthFunction_index_le_two_pow
-- name    : VapnikChervonenkis.GrowthFunction.index_le_two_pow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:34:19.846198+00:00
-- url     : https://prove2.me/theorems/98d92d19-e7bf-4705-9e8a-b47b0bd3416b
-- title:
--   The index is at most 2^r
-- statement:
--   Let $X$ be a set, $S$ a collection of subsets of $X$, and $x_1, \dots, x_r$ a sample of $r$ elements of $X$ (repetitions allowed). The index $\Delta^S(x_1, \dots, x_r)$, the number of different subsamples induced in the sample by the sets of $S$, satisfies
--
--   $$
--   \Delta^S(x_1, \dots, x_r) \le 2^r .
--   $$
--
--   Consequently $m^S(r) \le 2^r$ for every $r$; the proof of Theorem 1 opens with this fact.
--
--   **Formalization Note.** The sample is `x : Fin r → X`, and the index counts distinct position sets `{i | x i ∈ A}` with $A \in S$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 265, Subsection 1 (sentence before the definition of m^S(r))

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 265, Subsection 1: "Obviously, `Δ^S(x_1, ···, x_r)` is
always at most `2^r`." -/
theorem index_le_two_pow {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := by sorry

end VapnikChervonenkis.GrowthFunction
