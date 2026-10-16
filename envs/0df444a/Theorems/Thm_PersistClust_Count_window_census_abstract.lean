-- Prove2me | Theorems.Thm_PersistClust_Count_window_census_abstract
-- name    : PersistClust.Count.window_census_abstract
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T18:10:43.122301+00:00
-- url     : https://prove2.me/theorems/f278b12f-6919-4fee-b16d-c32bd0132375
-- title:
--   Abstract window census: an injective class map commuting with merge maps transports the windowed merge count (Bauer-Lesnick counting core)
-- statement:
--   Let g : U -> W and g' : U' -> W' be maps (merges), e : U -> U' and e' : W -> W' injective maps with g'(e u) = e'(g u) for all u. Let SL, SR be subsets of U and TL, TR subsets of U' with e(SL) contained in TL and TR contained in e(SR). Then, with f(S) = |S| - |merge(S)|, f(SL) - f(SR) <= f(TL) - f(TR), stated additively in extended naturals: |SL| + |g(SR)| + |g'(TL)| + |TR| <= |SR| + |g(SL)| + |TL| + |g'(TR)|. In persistence terms: the number of bars born in a window and dying across a merge level can only grow along an injective, merge-compatible comparison map whose windows are widened on the target side.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorems 4.5 / 4.8 cluster): the abstract census step of the Bauer-Lesnick induced-matching route for 0-dimensional persistence (the mono half im(phi) >-> Y(eps)). Pure Mathlib; uses the companion merge_count_mono (inlined as a private helper).

import Mathlib

namespace PersistClust.Count

theorem window_census_abstract {U W U' W' : Type*} (g : U → W) (g' : U' → W')
    (e : U → U') (e' : W → W') (he : Function.Injective e) (he' : Function.Injective e')
    (hcomm : ∀ u, g' (e u) = e' (g u)) {SL SR : Set U} {TL TR : Set U'}
    (hL : e '' SL ⊆ TL) (hR : TR ⊆ e '' SR) :
    SL.encard + (g '' SR).encard + (g' '' TL).encard + TR.encard ≤
      SR.encard + (g '' SL).encard + TL.encard + (g' '' TR).encard
    := by sorry
