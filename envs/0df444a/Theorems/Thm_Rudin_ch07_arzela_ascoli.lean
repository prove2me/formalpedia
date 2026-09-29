-- Prove2me | Theorems.Thm_Rudin_ch07_arzela_ascoli
-- name    : Rudin.ch07_arzela_ascoli
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T00:21:30.955787+00:00
-- url     : https://prove2.me/theorems/4a5af94e-9dbb-4214-861d-f3ef8cbdcec6
-- title:
--   Theorems 7.24-7.25 — Arzelà–Ascoli
-- statement:
--   Let $K$ be a compact metric space and $\{f_n\}$ a sequence of continuous complex functions on $K$ which is pointwise bounded and equicontinuous. Then $\{f_n\}$ is uniformly bounded and contains a uniformly convergent subsequence.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, pp. 157-158, Theorems 7.24 and 7.25

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorems 7.24 and 7.25 (Arzelà–Ascoli): a pointwise bounded, equicontinuous sequence
of continuous functions on a compact metric space is uniformly bounded and has a uniformly
convergent subsequence. -/
theorem ch07_arzela_ascoli {K : Type*} [MetricSpace K] [CompactSpace K] (f : ℕ → K → ℂ)
    (hcont : ∀ n, Continuous (f n))
    (hbdd : PointwiseBoundedOn f Set.univ) (heq : EquicontinuousOn f Set.univ) :
    UniformlyBoundedOn f Set.univ ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : K → ℂ,
      TendstoUniformlyOn (fun k => f (φ k)) g atTop Set.univ := by sorry

end Rudin
