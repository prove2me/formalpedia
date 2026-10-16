-- Prove2me | Theorems.Thm_PersistClust_Count_merge_count_mono
-- name    : PersistClust.Count.merge_count_mono
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T18:05:45.414793+00:00
-- url     : https://prove2.me/theorems/040d2dd6-8792-41d7-8c0a-993b02e6a82a
-- title:
--   Merge-count monotonicity: |S| + |g(S')| <= |S'| + |g(S)| for S a subset of S' (the functional |S| - |g(S)| is monotone)
-- statement:
--   Let g : U -> W be any map and S a subset of S' subsets of U. Then encard S + encard (g '' S') <= encard S' + encard (g '' S). Equivalently (for finite sets) the merge-count functional f(S) = |S| - |g(S)| -- the number of elements of S collapsed by g -- is monotone under inclusion: each added element raises |S| by one and |g(S)| by at most one. Stated additively in extended naturals, so no finiteness is needed.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / 4.8 cluster): the counting core of the Bauer-Lesnick induced-matching route for 0-dimensional persistence, where g is a structure (merge) map between component sets and f(S_L) - f(S_R) counts the bars born in a window that die across the merge level. Pure Mathlib.

import Mathlib

namespace PersistClust.Count

theorem merge_count_mono {U W : Type*} (g : U → W) {S S' : Set U} (h : S ⊆ S') :
    S.encard + (g '' S').encard ≤ S'.encard + (g '' S).encard
    := by sorry
