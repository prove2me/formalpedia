-- Prove2me | Theorems.Thm_Rudin_ch06_riemann_criterion
-- name    : Rudin.ch06_riemann_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:13:55.227762+00:00
-- url     : https://prove2.me/theorems/2aad433f-9d5d-47bf-b44a-d919ee518723
-- title:
--   Theorem 6.6 — the $\varepsilon$ criterion for integrability
-- statement:
--   A bounded $f$ satisfies $f \in \mathcal{R}(\alpha)$ on $[a,b]$ if and only if for every $\varepsilon > 0$ there is a partition $P$ with $U(P,f,\alpha) - L(P,f,\alpha) < \varepsilon$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 124, Theorem 6.6

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.6: a bounded `f` is integrable with respect to a monotonically increasing
`α` on `[a, b]` if and only if for every `ε > 0` there is a partition `P` with
`U(P, f, α) - L(P, f, α) < ε`. -/
theorem ch06_riemann_criterion (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    RSIntegrable a b f α ↔
      ∀ ε : ℝ, 0 < ε → ∃ P : Partition a b, upperSum f α P - lowerSum f α P < ε := by sorry

end Rudin
