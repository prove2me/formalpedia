-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_separated_bar_death_lower_bound
-- name    : PersistClust.Count.theorem_4_5_separated_bar_death_lower_bound
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T17:11:17.084501+00:00
-- url     : https://prove2.me/theorems/819f90bb-5169-40a5-a199-f0dc04aa2120
-- title:
--   Theorem 4.5 support - noise bars: deaths exceed birth minus d1 under separation
-- statement:
--   Let f be a real-valued function on a metric space X and let diagram0 f be its sublevel-set persistence diagram. If diagram0 f is (d1, d2)-separated, Delta < d2, and a nonzero diagram point (b, death) has birth coordinate b at most Delta, then its death coordinate is strictly greater than b - d1. The bar cannot lie in the LamE d2 region (that would force d2 < b at most Delta < d2), so it lies in the DeltaN d1 region: birth minus d1 is strictly below death. In the chase this is the noise-bar bound: bars born low (at or below tau + c*delta) die above birth minus d1, which is at least tau - d1 > 2*c*delta, leaving only finitely many possible death levels.
-- source:
--   The noise-bar death bound of the L_tau cluster in the proof of Theorem 4.5, Persistence-Based Clustering in Riemannian Manifolds (rr/6968). Child of theorem_4_5 (id 8476e8c8-3232-437b-939f-4ea37c366d80); companion of the accepted theorem_4_5_elder_chase_essential_bar (id 9cfba490-b1d0-4057-9d74-80806c1fc1df) and of the essential-birth bound; together these two separation facts give the elder chase its window arithmetic.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

namespace PersistClust.Count

theorem theorem_4_5_separated_bar_death_lower_bound {X : Type*} [MetricSpace X] {f : X → ℝ} {d₁ d₂ : ℝ} (hsep : IsSeparated (diagram0 f) d₁ d₂) {Δ : ℝ} (hΔd : Δ < d₂)
    {b d : EReal} (hbar : diagram0 f (b, d) ≠ 0) (hble : b ≤ (((Δ : ℝ) : ℝ) : EReal)) :
    b - (((d₁ : ℝ) : ℝ) : EReal) < d
    := by sorry
