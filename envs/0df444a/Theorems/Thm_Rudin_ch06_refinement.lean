-- Prove2me | Theorems.Thm_Rudin_ch06_refinement
-- name    : Rudin.ch06_refinement
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:05:05.265439+00:00
-- url     : https://prove2.me/theorems/22944e0b-c7bc-4e9b-9bd9-017f8812c1cb
-- title:
--   Theorem 6.4 — refinement moves the sums together
-- statement:
--   If $P'$ is a refinement of $P$ then $L(P,f,\alpha) \le L(P',f,\alpha)$ and $U(P',f,\alpha) \le U(P,f,\alpha)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 122, Definition 6.3 and Theorem 6.4

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.4: refining a partition increases the lower sum and decreases the upper
sum. -/
theorem ch06_refinement (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (P P' : Partition a b) (hrefine : Refines P' P) :
    lowerSum f α P ≤ lowerSum f α P' ∧ upperSum f α P' ≤ upperSum f α P := by sorry

end Rudin
