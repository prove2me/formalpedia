-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_linear_shatter_packing
-- name    : SmallClassesNeighbourhood.Linear.linear_shatter_packing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:50.194128+00:00
-- url     : https://prove2.me/theorems/90467c5f-6ed7-4ea6-b23f-7b8f74e55365
-- title:
--   Corollary 10 — packing with linear shatter bound
-- statement:
--   For all sufficiently large integers C, let A be a finite set of size n>C^10 and H a family of subsets of A. Suppose every nonempty U⊆A has at most C|U| traces from H. Every C^10-separated subfamily R⊆H satisfies
--
--   $$|R|\le n/C^7.$$
--
--   The quotient is real. Empty H and VC dimension zero are included. This is the packing bound used for the canonical separated representatives.
--
--   Differences from the source:
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Corollary 10, printed p. 7 (PDF p. 8)

import Definitions.Def_SmallClassesNeighbourhood_Linear_setSystems

namespace SmallClassesNeighbourhood.Linear

theorem linear_shatter_packing :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C : ℕ, L ≤ C →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (A : Finset V) (ℋ ℛ : Finset (Finset V)),
      C ^ 10 < A.card → (∀ X ∈ ℋ, X ⊆ A) →
      (∀ U : Finset V, U ⊆ A → U.Nonempty → (familyTraces ℋ U).card ≤ C * U.card) →
      ℛ ⊆ ℋ → Separated (C ^ 10) ℛ → (ℛ.card : ℝ) ≤ (A.card : ℝ) / (C : ℝ) ^ 7 := by sorry

end SmallClassesNeighbourhood.Linear
