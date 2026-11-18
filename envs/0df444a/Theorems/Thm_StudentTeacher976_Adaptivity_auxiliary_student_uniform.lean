-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_student_uniform
-- name    : StudentTeacher976.Adaptivity.auxiliary_student_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:31:36.576133+00:00
-- url     : https://prove2.me/theorems/3e9cb050-5bdc-4758-9091-0444ad54561b
-- title:
--   The witness-retaining auxiliary student is uniform
-- statement:
--   Let $L$ have a bounded existential witness presentation with predicate in $\Delta_{i+1}^p$, and let $r$ satisfy the admissible round conditions. The concrete witness-retaining auxiliary student is realized by one uniform oracle transducer:
--
--   $$
--   f_{L,r}\in\mathrm{FP}^{\Sigma_i^p}.
--   $$
--
--   Its input consists of the raw instance, the unary round number, and all previous reply batches in the published self-delimiting encoding. It halts on every bit string, with a single polynomial clock. This formalizes the computational uniformity of the p.19 upper-round construction; it asserts no winning property.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 p.19, upper-round witness retention construction; Definitions 1.1–1.2 pp.6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary

namespace StudentTeacher976.Adaptivity

theorem auxiliary_student_uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    UniformStudent i (auxiliaryStudent W r) := by sorry

end StudentTeacher976.Adaptivity
