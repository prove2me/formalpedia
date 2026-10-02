-- Prove2me | Theorems.Thm_ProcessingNetworks_GlobalStability_workload_witness_existence
-- name    : ProcessingNetworks.GlobalStability.workload_witness_existence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:15:25.98556+00:00
-- url     : https://prove2.me/theorems/9fa753f9-ee99-4d8e-a2cf-5f9c4c175962
-- title:
--   Lemma 8.27 — existence of a Lyapunov weight vector (milestone)
-- statement:
--   **Lemma 8.27.** Assume (8.47)-(8.49) hold. Then there exist a five-vector $x > 0$ and a
--   scalar $\varepsilon > 0$ satisfying (8.59)-(8.67) (Lemma 8.26's hypotheses, all
--   simultaneously).
--
--   This is the geometric heart of Theorem 8.25's sufficiency proof: (8.47)-(8.49) carve out a
--   non-empty region of admissible weight vectors, found by intersecting a parallelogram
--   (Figure 8.4(a), from (8.64)-(8.67)) with a wedge (Figure 8.4(b), from (8.59)-(8.60)) and
--   separately solving an analogous system for $(x_1,x_3,x_5)$ (Figure 8.5).
--
--   **Formalization note.** All nine conditions (8.59)-(8.67) are bundled into a single
--   existential conclusion, exactly matching the book's "there exist $x>0$ and $\varepsilon>0$
--   such that (8.59)-(8.67) hold"; per this mission's own `BRIEF.md` pitfall note, $x$ and
--   $\varepsilon$ are existentially quantified witnesses local to this lemma, not exposed in the
--   goal theorem's own statement.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 158, Lemma 8.27

import Mathlib

namespace ProcessingNetworks.GlobalStability

/-- Lemma 8.27, Dai & Harrison p. 158 (PDF p. 174): assume conditions (8.47)-(8.49) are
satisfied. Then there exist a five-vector `x > 0` and a scalar `ε > 0` such that (8.59)-(8.67)
hold. -/
theorem workload_witness_existence
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (h47 : lam1 * (m1 + m3 + m5) < 1) (h48 : lam1 * (m2 + m4) < 1) (h49 : lam1 * (m2 + m5) < 1) :
    ∃ x1 x2 x3 x4 x5 ε : ℝ, 0 < x1 ∧ 0 < x2 ∧ 0 < x3 ∧ 0 < x4 ∧ 0 < x5 ∧ 0 < ε ∧
      lam1 * (x2 + x4) + ε ≤ x2 / m2 ∧ lam1 * (x2 + x4) + ε ≤ x4 / m4 ∧
      lam1 * (x1 + x3 + x5) + ε ≤ x1 / m1 ∧ lam1 * (x1 + x3 + x5) + ε ≤ x3 / m3 ∧
      lam1 * (x1 + x3 + x5) + ε ≤ x5 / m5 ∧
      x2 + x4 ≤ x1 + x3 + x5 ∧ x4 ≤ x3 + x5 ∧
      x3 + x5 ≤ x2 + x4 ∧ x5 ≤ x4 := by sorry

end ProcessingNetworks.GlobalStability
