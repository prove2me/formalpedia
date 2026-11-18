-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_student_protocol
-- name    : StudentTeacher976.Adaptivity.auxiliary_student_protocol
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:25.491277+00:00
-- url     : https://prove2.me/theorems/7deb3f70-75e1-49f6-8d90-aa7faea4daf0
-- title:
--   The canonical upper-round student has a polynomial oracle protocol
-- statement:
--   Fix a hierarchy level $i$, a witness presentation for a language $L$, and an admissible round function $r$. There exist one oracle $O$ from $\Sigma_i^p$, one polynomial-time pure CPU, an output function $F$, and polynomial bounds on oracle calls and intermediate encoded sizes, valid on all raw input strings. For every input $x$, round $t$, and preceding reply history $H$,
--
--   $$
--   F(\langle x,1^{t+1},\langle H\rangle\rangle)
--   =\langle S_{W,r}(x,t,H)\rangle.
--   $$
--
--   Here $S_{W,r}$ is the published canonical student: it retains valid witnesses from prior refutations, supplies fixed zero fillers otherwise, and emits an empty batch beyond the round budget. Histories in this statement need not be legal. The protocol supplies the algorithmic part of one uniform oracle transducer, without a promise about malformed machine inputs.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), Definition 1.2 p.7 and §3.1 pp.19–20; the published finite oracle-machine interface and concrete Cslib/complexitylib polynomial-time machine calculus. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
import Definitions.Def_StudentTeacher976_Adaptivity_OracleProtocol
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl
open Turing.MultiTapeTM

namespace StudentTeacher976.Adaptivity

theorem auxiliary_student_protocol (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    ∃ (O : Oracle) (cpu F : Word → Word) (T B : Polynomial ℕ),
      {x | O x = true} ∈ Sigma i ∧
      ComputableInPolyTime cpu encBits encBits ∧
      (∀ x : Word, ∃ steps ≤ T.eval x.length,
        OracleDriver.Trace cpu O (B.eval x.length) (OracleDriver.shifted x) (F x) steps) ∧
      ∀ (x : Word) (t : ℕ) (H : List (List Word)),
        F (tup [x, List.replicate (t+1) true, tup (H.map tup)]) =
          tup (auxiliaryStudent W r x t H) := by sorry

end StudentTeacher976.Adaptivity
