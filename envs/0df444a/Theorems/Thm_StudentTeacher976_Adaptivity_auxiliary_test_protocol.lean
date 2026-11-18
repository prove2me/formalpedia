-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_test_protocol
-- name    : StudentTeacher976.Adaptivity.auxiliary_test_protocol
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:15.789198+00:00
-- url     : https://prove2.me/theorems/b22679ba-6a64-4eff-a0bd-695b3c049a5e
-- title:
--   The canonical auxiliary test has a polynomial oracle protocol
-- statement:
--   Fix a hierarchy level $i$, a witness presentation for a language $L$, and an admissible round function $r$. There exist one oracle $O$ from $\Sigma_i^p$, one polynomial-time pure CPU, one output function $F$, and polynomial bounds on the protocol's oracle-call count and intermediate encoded sizes, valid on every raw input string. The output's first bit, defaulting to false, satisfies
--
--   $$
--   \operatorname{head}(F(s))=1
--   \iff
--   \exists x,y,z:\ s=\langle x,y,z\rangle\ \land\ \operatorname{AuxTest}_{W,r}(x,y,z).
--   $$
--
--   The predicate is the published canonical auxiliary test, including malformed input and output handling, raw block lengths, exact witness lengths, and the witness implication. This protocol provides the algorithmic part of its deterministic oracle decision procedure; the separately verified protocol compiler supplies the finite machine.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), Definition 1.2 p.7 and §3.1 pp.19–20; the published finite oracle-machine interface and concrete Cslib/complexitylib polynomial-time machine calculus. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
import Definitions.Def_StudentTeacher976_Adaptivity_OracleProtocol
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl
open Turing.MultiTapeTM

namespace StudentTeacher976.Adaptivity

theorem auxiliary_test_protocol (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    ∃ (O : Oracle) (cpu F : Word → Word) (T B : Polynomial ℕ),
      {x | O x = true} ∈ Sigma i ∧
      ComputableInPolyTime cpu encBits encBits ∧
      (∀ x : Word, ∃ steps ≤ T.eval x.length,
        OracleDriver.Trace cpu O (B.eval x.length) (OracleDriver.shifted x) (F x) steps) ∧
      ∀ s : Word, (F s).head?.getD false = true ↔
        ∃ x y z, s = tup [x,y,z] ∧ auxiliaryTest W r x y z := by sorry

end StudentTeacher976.Adaptivity
