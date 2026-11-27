-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_Supplement_theorem_3_11
-- name    : UniformPrecSched.Makespan.Supplement.theorem_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:24:57.21869+00:00
-- url     : https://prove2.me/theorems/de10e567-f5c2-4a1d-8d35-40b7eeb923e9
-- title:
--   Theorem 3.11 — an unbounded integer-relaxation makespan gap
-- statement:
--   There is an absolute constant $c>0$ such that for every machine-count threshold $M$ there is a nonempty instance of precedence-constrained nonpreemptive scheduling on $m\ge\max\{M,4\}$ uniformly related machines, an attained positive optimum $D^*$ of the integer relaxation (1)–(6), and an optimal feasible schedule of makespan $C^*_{\max}$ such that
--
--   $$C^*_{\max}\ge c\frac{\log_2m}{\log_2\log_2m}D^*.$$
--
--   Thus even binary speed-class assignments leave an asymptotically unbounded gap between the relaxation and actual scheduling. The comparator is the integer optimum, not the fractional LP optimum. Positivity and actual minimizing witnesses prevent degenerate ratio or infimum readings.
--
--   Differences from the source:
--   - encoding: an Ω(log m/log log m) gap on a family of instances → one c>0 before every machine-count threshold M, with witnesses m≥max(M,4), n>0 and D*>0; reason: expresses an unbounded asymptotic family and excludes undefined or zero ratio denominators, without removing its large instances
--   - encoding: the integer optimum D* and optimal makespan C*max → a feasible integer-minimizing triple and a feasible makespan-minimizing schedule; reason: retains attainment and the integer comparator explicitly instead of using totalized infima
--   - encoding: log m and log log m → log₂m and log₂(log₂m); reason: uses the paper’s p. 10 logarithm convention
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 10 (PDF 10), Theorem 3.11; p. 11 (PDF 11), proof

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Supplement_Integral

namespace UniformPrecSched.Makespan.Supplement

/-- Chudak–Shmoys, authors' manuscript, p. 10 (proof p. 11), PDF 10–11,
Theorem 3.11. An unbounded family with positive attained integer optima and actual
optimal schedules. The absolute constant is outside every size threshold.
Formalization Note: log is base two; m≥4 keeps log log positive. -/
theorem theorem_3_11 :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ (n m : ℕ) (I : Instance n m)
      (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ) (D : ℝ)
      (σ : Schedule I),
      M ≤ m ∧ 4 ≤ m ∧ 0 < n ∧ 0 < D ∧ IPOptimal I x C D ∧
      IsMakespanOptimal I σ ∧
      c * (Real.logb 2 m / Real.logb 2 (Real.logb 2 m)) * D ≤ σ.makespan := by sorry

end UniformPrecSched.Makespan.Supplement
