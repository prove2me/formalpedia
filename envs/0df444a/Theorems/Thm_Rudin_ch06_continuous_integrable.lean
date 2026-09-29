-- Prove2me | Theorems.Thm_Rudin_ch06_continuous_integrable
-- name    : Rudin.ch06_continuous_integrable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:13:39.418234+00:00
-- url     : https://prove2.me/theorems/52058224-8aa2-497d-9d8b-4aa8e12f9a4d
-- title:
--   Theorem 6.8 — continuous functions are integrable
-- statement:
--   If $f$ is continuous on $[a,b]$ then $f \in \mathcal{R}(\alpha)$ for every monotonically increasing $\alpha$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 124, Theorem 6.8

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.8: a continuous function on `[a, b]` is integrable with respect to every
monotonically increasing `α`. -/
theorem ch06_continuous_integrable (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : ContinuousOn f (Set.Icc a b)) :
    RSIntegrable a b f α := by sorry

end Rudin
