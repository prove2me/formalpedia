-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_presented_adaptivity_separation
-- name    : StudentTeacher976.Adaptivity.presented_adaptivity_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:24:17.031077+00:00
-- url     : https://prove2.me/theorems/7469b54e-9323-4d7c-9c87-c1625ce04342
-- title:
--   Adaptivity separation for a fixed refutable presentation
-- statement:
--   Let $i\ge0$ and suppose $\Sigma_{i+1}^p\not\subseteq\Delta_{i+1}^p/\mathrm{poly}$. Let $r$ be a polynomial-time, nondecreasing, unbounded round function with $1\le r(m)\le m^{1-\varepsilon}$ at positive lengths for some $\varepsilon>0$, and let $q$ be a positive polynomial-time, polynomially bounded query function. There are a total bounded search relation $R$ and a refutable presentation $P$ of $R$, with a $\Delta_{i+1}^p$ test, such that
--
--   $$
--   P\text{ has an }(r+1,1)\text{ uniform winning student, but has no }(r,q)\text{ uniform winning student}.
--   $$
--
--   Both students are measured against this same presentation. This result isolates the operational separation proved by the witness-tuple and advice-cover construction; it does not exclude students using other faithful presentations of $R$.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Theorem 1.4, p.7, fixed-predicate construction in §3.1, pp.19–21.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.presented_adaptivity_separation (i : ℕ) (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i+1)⊆DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ∃ (R : SearchRelation) (P : RefutablePresentation i R),
      (∃ g : Student,UniformStudent i g ∧ StudentShape P (fun m => r m+1) (fun _ => 1) g ∧
        StudentWins P (fun m => r m+1) (fun _ => 1) g) ∧
      ¬∃ g : Student,UniformStudent i g ∧ StudentShape P r q g ∧ StudentWins P r q g := by sorry
