-- Prove2me | Theorems.Thm_PersistClust_Count_interval_hall_counting
-- name    : PersistClust.Count.interval_hall_counting
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T22:11:53.240319+00:00
-- url     : https://prove2.me/theorems/97f0db8d-8308-44c9-a471-619d9769f2f2
-- title:
--   Convex-bipartite Hall (counting form): demands with interval neighbourhoods satisfy Hall's inequality when every window holds enough supply
-- statement:
--   Let s be a finite set of demands x with real intervals [lo x, hi x] (lo x <= hi x), and let every supply point q have a real position pos q. Suppose that for every window A <= B, the number of demands of s whose whole interval lies in [A, B] is at most the number of supply points with position in [A, B]. Then |s| is at most the number of supply points lying in the interval of some demand of s (Hall's inequality for interval neighbourhoods). Cardinalities are encard of sets; supply sets may be infinite.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the one-dimensional Hall step of the induced-matching route for the QSE sector, where demand copies have neighbourhoods of different widths in the death coordinate. Pure Mathlib; the core is proved for any linear order.

import Mathlib

namespace PersistClust.Count

theorem interval_hall_counting {X Q : Type} (lo hi : X → ℝ) (pos : Q → ℝ)
    (s : Set X) (hs : s.Finite) (hlohi : ∀ x ∈ s, lo x ≤ hi x)
    (hwin : ∀ A B : ℝ, A ≤ B →
      {x ∈ s | A ≤ lo x ∧ hi x ≤ B}.encard ≤ {q : Q | A ≤ pos q ∧ pos q ≤ B}.encard) :
    s.encard ≤ (⋃ x ∈ s, {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}).encard
    := by sorry
