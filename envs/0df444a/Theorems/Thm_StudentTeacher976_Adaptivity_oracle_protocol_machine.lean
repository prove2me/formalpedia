-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_oracle_protocol_machine
-- name    : StudentTeacher976.Adaptivity.oracle_protocol_machine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:14.769563+00:00
-- url     : https://prove2.me/theorems/b692c1a0-c560-42ea-8f7b-c3d906f419ea
-- title:
--   Bounded pure-CPU oracle protocols compile to one finite oracle machine
-- statement:
--   Let $C$ be a polynomial-time pure binary string function serving as the CPU of the published framed query protocol. There is one finite two-tape oracle machine $M$, chosen before the oracle and all resource bounds, with the following property.
--
--   For any oracle $O$, output function $f$, and polynomials $T,B$, suppose that every input $x$ has a protocol execution beginning with its two-zero-bit initialization prefix, ending with $f(x)$, using at most $T(|x|)$ oracle calls, and keeping all CPU requests and responses within $B(|x|)$ bits. Then there is one polynomial clock $p$ such that
--
--   $$
--   M^O(x)\text{ halts within }p(|x|)\text{ steps and outputs }f(x)
--   \qquad\text{for every }x.
--   $$
--
--   Its Boolean result is the first output bit, defaulting to false. The oracle is unrestricted. This theorem supplies the operational compiler used when pure list processing is interleaved with actual oracle calls in a student or refutation test.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), Definition 1.2 p.7 and §3.1 pp.19–20; the published finite oracle-machine interface and concrete Cslib/complexitylib polynomial-time machine calculus. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_OracleProtocol
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl
open Turing.MultiTapeTM
open StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.oracle_protocol_machine (cpu : Word → Word)
     (hcpu : ComputableInPolyTime cpu encBits encBits) :
     ∃ M : OTM, ∀ (O : Oracle) (f : Word → Word) (T B : Polynomial ℕ),
       (∀ x : Word, ∃ steps ≤ T.eval x.length,
         OracleDriver.Trace cpu O (B.eval x.length) (OracleDriver.shifted x) (f x) steps) →
       ∃ clock : Polynomial ℕ, ∀ x : Word,
         M.result O x (clock.eval x.length) = some ((f x).head?.getD false) ∧
         M.output O x (clock.eval x.length) = f x := by sorry
