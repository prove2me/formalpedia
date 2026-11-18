-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_finite_control_compilation
-- name    : StudentTeacher976.Adaptivity.finite_control_compilation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:39:34.363434+00:00
-- url     : https://prove2.me/theorems/1f1f0b93-7052-457d-982c-ca158cf1c5ae
-- title:
--   Finite-control oracle programs compile to finite two-tape machines
-- statement:
--   Let $P$ be an operational two-tape program with fixed finite control and tape alphabet. There is a single finite oracle Turing machine $M$, chosen independently of the oracle and input, such that whenever $P^O(x)$ halts after $t$ symbolic steps with Boolean result $b$ and work-tape output $y$,
--
--   $$
--   M^O(x)\text{ halts with result }b\text{ and output }y\text{ within }3t+1\text{ steps}.
--   $$
--
--   The same oracle is retained. The statement includes exact output equality, empty inputs and all finite halting times. This provides the implementation bridge used by explicit parser, padding and student programs.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7 and §3.1 p.19. Operational simulation and exact-quantifier padding bridges for the published machine definitions. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl

theorem StudentTeacher976.Adaptivity.finite_control_compilation {Q A : Type} [Fintype Q] [Fintype A]
    (P : QAdvFew.PoQOracle.OTM.FiniteControl.Program Q A) :
    ∃ M : QAdvFew.PoQOracle.OTM, ∀ (O : QAdvFew.PoQOracle.Oracle)
      (x : List Bool) (t : ℕ) (b : Bool),
      (((P.step O)^[t]) (P.initial x)).state = Sum.inl b →
      M.result O x (3*t+1) = some b ∧
      M.output O x (3*t+1) =
        QAdvFew.PoQOracle.OTM.FiniteControl.readWord
          (((P.step O)^[t]) (P.initial x)).work (((P.step O)^[t]) (P.initial x)).whi := by sorry
