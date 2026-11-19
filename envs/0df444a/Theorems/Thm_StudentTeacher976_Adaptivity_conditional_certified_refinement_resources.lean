-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_conditional_certified_refinement_resources
-- name    : StudentTeacher976.Adaptivity.conditional_certified_refinement_resources
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T21:39:38.751841+00:00
-- url     : https://prove2.me/theorems/bf7b83f5-b6a8-4d6a-a3a1-8f3beee17f44
-- title:
--   Certified replacements need exist only when the default answer fails
-- statement:
--   Let $R$ be a total polynomially bounded search relation with a refutable presentation at hierarchy level $i$. Let $e$ denote the empty answer string. Suppose a predicate $V$, decidable in $\Delta_{i+1}^p$, and a polynomial $c$ satisfy
--
--   $$
--   \begin{aligned}
--   |v|=c(|x|)\ \wedge\ V(x,y,v)&\ \Longrightarrow\ R(x,y),\\
--   \neg R(x,e)&\ \Longrightarrow\ \exists y,v\quad |v|=c(|x|)\ \wedge\ V(x,y,v).
--   \end{aligned}
--   $$
--
--   Thus certificates soundly identify valid answers. They need exist only on inputs where the empty default answer is invalid.
--
--   Let $r,q$ be polynomial-time length functions whose effective resource counts are positive at every length, and suppose that at least two rounds are available at all sufficiently large lengths. Then
--
--   $$
--   R\in\mathrm{ST}^{\Sigma_i^p}[r,q].
--   $$
--
--   Membership permits a different faithful refutation presentation of the same underlying relation and evaluates the unchanged resource functions at the same raw input lengths. This extends the total certified-refinement construction to refinements that need cover only the inputs where a fixed default answer fails. The empty input uses the published length-one resource convention.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definitions 1.1–1.2, pp.6–7. Derived generalization of the mission development's total certified-refinement theorem: certificate existence is required only when the empty default answer is invalid. This auxiliary construction is not asserted in the source.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.conditional_certified_refinement_resources {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
    (heff : {s | ∃ x y z, s = tup [x,y,z] ∧ V x y z} ∈ Delta i)
    (hsound : ∀ x y v, v.length = c.eval x.length → V x y v → R x y)
    (htotal : ∀ x, ¬ R x [] → ∃ y v, v.length = c.eval x.length ∧ V x y v)
    (r q : ℕ → ℕ) (hr : PolyTimeLength r) (hq : PolyTimeLength q)
    (hrpos : ∀ n, 1 ≤ resource r n) (hqpos : ∀ n, 1 ≤ resource q n)
    (hevent : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ resource r n) : R ∈ ST i r q := by sorry
