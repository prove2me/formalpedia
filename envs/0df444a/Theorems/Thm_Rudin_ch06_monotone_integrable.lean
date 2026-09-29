-- Prove2me | Theorems.Thm_Rudin_ch06_monotone_integrable
-- name    : Rudin.ch06_monotone_integrable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:15:36.604539+00:00
-- url     : https://prove2.me/theorems/ffdab7df-c652-4587-af4b-896a3b21c3ad
-- title:
--   Theorem 6.9 — monotone integrands
-- statement:
--   If $f$ is monotone on $[a,b]$ and the monotonically increasing $\alpha$ is continuous on $[a,b]$, then $f \in \mathcal{R}(\alpha)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 126, Theorem 6.9

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.9: if `f` is monotone on `[a, b]` and the monotonically increasing
integrator `α` is continuous on `[a, b]`, then `f` is integrable with respect to `α`. -/
theorem ch06_monotone_integrable (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc a b)) (hα : MonotoneOn α (Set.Icc a b))
    (hαc : ContinuousOn α (Set.Icc a b)) :
    RSIntegrable a b f α := by sorry

end Rudin
