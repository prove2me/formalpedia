-- Prove2me | Theorems.Thm_Rudin_ch07_uniform_limit_continuous
-- name    : Rudin.ch07_uniform_limit_continuous
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:21:00.856953+00:00
-- url     : https://prove2.me/theorems/65921e87-2e17-48ec-bb7d-f6a3b7376e5f
-- title:
--   Theorem 7.12 — uniform limits of continuous functions
-- statement:
--   If each $f_n$ is continuous on $E$ and $f_n \to g$ uniformly on $E$, then $g$ is continuous on $E$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 150, Theorem 7.12

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.12: a uniform limit of continuous functions is continuous. -/
theorem ch07_uniform_limit_continuous {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (hcont : ∀ n, ContinuousOn (f n) E) (huc : TendstoUniformlyOn f g atTop E) :
    ContinuousOn g E := by sorry

end Rudin
