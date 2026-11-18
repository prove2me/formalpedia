-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_test_efficient
-- name    : StudentTeacher976.Adaptivity.auxiliary_test_efficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:31:30.669511+00:00
-- url     : https://prove2.me/theorems/dc42e0f9-de35-4ce9-9ef6-e614b2bfe29f
-- title:
--   The canonical auxiliary predicate is efficiently decidable
-- statement:
--   Let $L$ have a bounded existential witness presentation with predicate in $\Delta_{i+1}^p$, and let $r$ satisfy the admissible round conditions. The canonical raw auxiliary predicate, including tuple parsing, length checks, and the coordinate-witness implication, belongs to the same decision class:
--
--   $$
--   \{\langle x,y,z\rangle:\varphi_{L,r}'(x,y,z)\}\in\Delta_{i+1}^p.
--   $$
--
--   Malformed triple encodings are rejected. The conclusion requires one fixed finite oracle machine, one oracle in $\Sigma_i^p$, and one polynomial clock valid on every string. This is the operational decision-complexity obligation in the upper-round construction on p.19.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 p.19, upper-round witness retention construction; Definitions 1.1–1.2 pp.6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary

namespace StudentTeacher976.Adaptivity

theorem auxiliary_test_efficient (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    {s | ∃ x y z, s = QAdvFew.PoQOracle.tup [x, y, z] ∧ auxiliaryTest W r x y z} ∈ Delta i := by sorry

end StudentTeacher976.Adaptivity
