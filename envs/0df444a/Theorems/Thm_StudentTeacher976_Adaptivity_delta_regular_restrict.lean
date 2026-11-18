-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_delta_regular_restrict
-- name    : StudentTeacher976.Adaptivity.delta_regular_restrict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:49:50.884224+00:00
-- url     : https://prove2.me/theorems/ecc75863-3a17-4d5e-b0b3-16f9fc1d471c
-- title:
--   Deterministic oracle computation admits finite syntax checks
-- statement:
--   Let $L\in\Delta_{i+1}^p$ be decided by one finite oracle machine with one polynomial clock, and let $D$ be a fixed finite automaton on binary words. Then
--
--   $$
--   L\cap L(D)\in\Delta_{i+1}^p.
--   $$
--
--   The same hierarchy level suffices, and the resulting machine halts on every string. This is the syntax-checking closure needed to reject malformed tuple encodings before evaluating a witness predicate.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, STOC 2027 submission #976 (October 2026), §1.2.1 pp.6–7, §3.1 p.19; finite oracle machines and tuple parsing in the pinned formalization; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_DFA

namespace StudentTeacher976.Adaptivity

theorem delta_regular_restrict {i : ℕ} {L : Language} (hL : L ∈ Delta i)
    (D : QAdvFew.PoQOracle.OTM.Precheck.DFA) :
    L ∩ {x | D.accept (D.run x) = true} ∈ Delta i := by sorry

end StudentTeacher976.Adaptivity
