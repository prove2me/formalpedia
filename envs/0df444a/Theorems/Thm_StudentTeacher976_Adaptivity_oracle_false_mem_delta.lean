-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_oracle_false_mem_delta
-- name    : StudentTeacher976.Adaptivity.oracle_false_mem_delta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:51:38.313938+00:00
-- url     : https://prove2.me/theorems/8f067edc-4cf9-49d7-b9ca-a8f9c77645e7
-- title:
--   A negative oracle answer is decidable in the same oracle class
-- statement:
--   Let $O$ be a binary oracle whose accepting language lies in $\Sigma_i^p$. The language of its negative answers is decided by a finite polynomial-time machine with that same oracle:
--
--   $$
--   \{x:O(x)=0\}\in\Delta_{i+1}^p.
--   $$
--
--   The machine and clock are fixed before the input, and the clock holds on all strings, including the empty word. This is the one-query oracle interface used when a witness predicate is the complement of a residual hierarchy language.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, STOC 2027 submission #976 (October 2026), §1.2.1 pp.6–7, §3.1 p.19; finite oracle machines and tuple parsing in the pinned formalization; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity

namespace StudentTeacher976.Adaptivity

theorem oracle_false_mem_delta (i : ℕ) (O : QAdvFew.PoQOracle.Oracle)
    (hO : {s | O s = true} ∈ Sigma i) :
    {s | O s = false} ∈ Delta i := by sorry

end StudentTeacher976.Adaptivity
