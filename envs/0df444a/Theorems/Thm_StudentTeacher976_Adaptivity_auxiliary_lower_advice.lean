-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_lower_advice
-- name    : StudentTeacher976.Adaptivity.auxiliary_lower_advice
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-17T23:12:52.002357+00:00
-- url     : https://prove2.me/theorems/9968efb1-f3f5-46e0-95ff-8af14112fdab
-- title:
--   A lower-round witness-tuple solver yields polynomial advice
-- statement:
--   Let $L$ have a bounded existential $\Delta_{i+1}^p$ witness presentation. Let $r$ and $q$ satisfy the resource conditions of Theorem 1.4. If the raw-input witness-tuple relation can be solved in $r(m)$ rounds with $q(m)$ parallel queries, then
--
--   $$
--   L\in\Delta_{i+1}^p/\mathrm{poly}.
--   $$
--
--   The advice is shared by all inputs of the same decision length and has one polynomial bound. The conclusion requires one fixed oracle machine and one polynomial clock on all strings. This is the lower-bound implication of the adaptivity proof on pp.19–21, with the raw size conversion of Appendix A. The premise is membership of the underlying relation through some faithful presentation, matching the main theorem's definition of the game class.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 pp.19–21, with Definitions 1.1–1.2 pp.6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion

namespace StudentTeacher976.Adaptivity

theorem auxiliary_lower_advice (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hgame : auxiliaryRelation W r ∈ ST i r q) :
    L ∈ DeltaPoly i := by sorry

end StudentTeacher976.Adaptivity
