-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_Supplement_theorem_7_2
-- name    : SkutellaCQP.MaxSNP.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:54:41.460602+00:00
-- url     : https://prove2.me/theorems/5f440b2f-cefc-4606-9fd3-ee76e725abea
-- title:
--   Theorem 7.2 — full MAX SNP hardness with the polynomial 32,1 L-reduction
-- statement:
--   The full unrelated parallel-machine scheduling problem with job-dependent release dates and unweighted total completion time is MAX SNP-hard:
--   $$R\mid r_j\mid\sum_j C_j\quad\text{is MAX SNP-hard under L-reductions}.$$
--   Hardness quantifies over every quantifier-free MAX SNP presentation, not only over the gadget family. The statement also supplies the cited unconditional hardness of 3-OCCURRENCE MAX3SAT and an actual L-reduction with constants $\alpha=32,\beta=1$, using precisely the source maps $R$ and SAT. Both transformations must have uniform finite-alphabet polynomial-time machines; valid inputs and feasible recovered solutions are required. No hardness assertion is assumed as a premise.
--
--   The scheduling problem includes zero processing requirements, forbidden machines through eligibility, arbitrary finite rational data, and rational start times. Its optimum agrees with the real-time optimum by left-justification. The numerical L-reduction goal remains an immutable published reference and is not re-stated as this hardness theorem.
--
--   Differences from the source:
--   - encoding: MAXSNP-hard and L-reduction → all quantifier-free relational MAX SNP presentations, with explicit finite-alphabet polynomial-time transformations and both L inequalities; reason: this supplies standard complexity semantics and includes the full target scheduling problem
--   - encoding: the reduction has two machines per variable → the same eligible machines plus one never-eligible dummy machine; reason: the empty instance then has a positive machine count; every nonempty feasible schedule and objective is preserved
--   - generalization: the scheduling hardness conclusion with cited source hardness and a proof of the reduction → the cited source hardness and the concrete polynomial 32,1 reduction are also conclusion conjuncts; reason: nothing is assumed away; the original hardness theorem is retained in full
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, p. 33, Theorem 7.2

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Hardness

namespace SkutellaCQP.MaxSNP.Supplement

/-- Theorem 7.2, p. 33: unconditional MAX SNP hardness of the full scheduling problem.
The cited source hardness and the concrete polynomial 32,1 L-reduction are supplied,
not assumed as premises. -/
theorem theorem_7_2 :
    MaxSNPHard occurrenceSatProblem ∧
    (∃ R : LReduction occurrenceSatProblem schedulingProblem, IsSourceReduction R) ∧
    MaxSNPHard schedulingProblem := by sorry

end SkutellaCQP.MaxSNP.Supplement
