-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_polynomial_transducer_normal_form
-- name    : StudentTeacher976.Adaptivity.polynomial_transducer_normal_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:12.268197+00:00
-- url     : https://prove2.me/theorems/c8fead06-e2a9-452f-a0e9-9087a23d8693
-- title:
--   Polynomial-time transducers have a clean finite-program normal form
-- statement:
--   Let $f$ be a binary string function computable by a finite binary multiple-tape machine in polynomial time. There exist finite control and work alphabets, a pure two-tape program $P$, and one polynomial $p$ such that, for every input $x$, the configuration after $p(|x|)$ steps is
--
--   $$
--   (\operatorname{halt}(\operatorname{head}(f(x))),\ \operatorname{bits}(f(x)),\ 0,\ \varnothing,\ 0).
--   $$
--
--   The Boolean result is the first output bit, defaulting to false. The work tape is exactly the output word, the query tape is blank, and both heads are at the origin. The program makes no oracle calls. This normal form permits repeated calls as subroutines in the canonical student and verifier implementations.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), Definition 1.2 p.7 and §3.1 pp.19–20; the published finite oracle-machine interface and concrete Cslib/complexitylib polynomial-time machine calculus. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List

theorem StudentTeacher976.Adaptivity.polynomial_transducer_normal_form
    {f : List Bool → List Bool}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits) :
    ∃ (Q Γ : Type) (_ : Fintype Q) (_ : Fintype Γ) (_ : DecidableEq Γ),
      ∃ P : QAdvFew.PoQOracle.OTM.FiniteControl.Program Q (Unit ⊕ Γ), ∃ clock : Polynomial ℕ,
        P.Pure ∧ ∀ x : List Bool,
          P.coreStep^[clock.eval x.length] (P.coreInitial x) =
            { state := Sum.inl ((f x).head?.getD false)
              work := QAdvFew.PoQOracle.OTM.FiniteControl.bitTape (f x)
              wh := 0
              query := fun _ => none
              qh := 0 } := by sorry
