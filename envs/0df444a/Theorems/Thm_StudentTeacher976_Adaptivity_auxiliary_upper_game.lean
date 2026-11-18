-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_upper_game
-- name    : StudentTeacher976.Adaptivity.auxiliary_upper_game
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:12:28.854122+00:00
-- url     : https://prove2.me/theorems/dfc656d6-61c1-4b46-9eb3-afd5b6a3548c
-- title:
--   The witness-tuple relation admits one extra round
-- statement:
--   Let $L$ have a bounded existential $\Delta_{i+1}^p$ witness presentation, and let $r$ satisfy the admissible round conditions of Theorem 1.4. The raw-input auxiliary relation asks for a witness for every positive coordinate of the decoded $r(m)$-tuple, at raw input length $m$. At lengths where the raw block decoding is unavailable it has the unique easy answer. Then
--
--   $$
--   R_{L,r}\in\mathrm{ST}^{\Sigma_i^p}[r(m)+1,1].
--   $$
--
--   This is the upper-bound construction on p.19: the student retains valid witnesses from prior teacher replies. The statement includes totality, polynomial bounds, a faithful refutable presentation, and one operationally uniform student on all input strings.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 pp.19–21, with Definitions 1.1–1.2 pp.6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion

namespace StudentTeacher976.Adaptivity

theorem auxiliary_upper_game (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    auxiliaryRelation W r ∈ ST i (fun m => r m + 1) (fun _ => 1) := by sorry

end StudentTeacher976.Adaptivity
