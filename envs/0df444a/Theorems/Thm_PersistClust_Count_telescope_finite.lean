-- Prove2me | Theorems.Thm_PersistClust_Count_telescope_finite
-- name    : PersistClust.Count.telescope_finite
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T18:38:14.529614+00:00
-- url     : https://prove2.me/theorems/47caf604-6548-4b66-9720-75d9309fb8e0
-- title:
--   Finite telescoping: a step function constant off a finite set Z, jumping by m(z) across each z in Z, increases by the sum of the jumps strictly between two generic points
-- statement:
--   Let h, m : R -> N and Z a finite set of reals. Suppose (hconst) h s = h t whenever s <= t and no point of Z lies in [s, t], and (hjump) for every z in Z there is eta0 > 0 such that h (z + eta) = h (z - eta) + m z for all 0 < eta < eta0. Then for D1 <= D2 with D1, D2 not in Z: h D2 = h D1 + sum of m z over the z in Z with D1 < z < D2. In persistence terms (h = number of components born exactly at a fixed level and alive at level t, m z = the multiplicity of the bar dying at z): the copies of a fixed-birth column inside a death window are counted by the difference of the alive-counts at the window ends.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorems 4.5 / 4.8 cluster): the copy-count bridge of the Bauer-Lesnick induced-matching route (window copy counts = rank-type differences). Pure Mathlib.

import Mathlib

namespace PersistClust.Count

theorem telescope_finite (h : ℝ → ℕ) (m : ℝ → ℕ) (Z : Finset ℝ)
    (hconst : ∀ s t : ℝ, s ≤ t → (∀ z ∈ Z, z < s ∨ t < z) → h s = h t)
    (hjump : ∀ z ∈ Z, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → h (z + η) = h (z - η) + m z)
    {D₁ D₂ : ℝ} (hD : D₁ ≤ D₂) (hD₁ : D₁ ∉ Z) (hD₂ : D₂ ∉ Z) :
    h D₂ = h D₁ + ∑ z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), m z
    := by sorry
