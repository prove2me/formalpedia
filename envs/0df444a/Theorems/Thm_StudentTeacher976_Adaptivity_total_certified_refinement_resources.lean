-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_total_certified_refinement_resources
-- name    : StudentTeacher976.Adaptivity.total_certified_refinement_resources
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T18:52:53.290633+00:00
-- url     : https://prove2.me/theorems/e138f905-7764-4b8d-a177-a6550d7f6214
-- title:
--   A total certified refinement suffices for two-round presentation membership
-- statement:
--   Let $R$ be a total polynomially bounded search relation with a refutable presentation at hierarchy level $i$. Suppose a predicate $V$, decidable in $\Delta_{i+1}^p$, and a polynomial $c$ satisfy
--
--   $$
--   \begin{aligned}
--   |v|=c(|x|)\ \wedge\ V(x,y,v)&\ \Longrightarrow\ R(x,y),\\
--   \forall x\ \exists y,v\quad |v|=c(|x|)&\ \wedge\ V(x,y,v).
--   \end{aligned}
--   $$
--
--   These conditions give a sound certificate for at least one valid answer on each input. Other valid answers need not have such certificates.
--
--   Let $r,q$ be polynomial-time length functions with positive effective resource counts at every length, and assume that the effective round count is at least two at all sufficiently large lengths. Then
--
--   $$
--   R\in\mathrm{ST}^{\Sigma_i^p}[r,q].
--   $$
--
--   Membership permits an alternative faithful refutation presentation of the same relation and preserves the original raw input length and resource functions. This strengthens the positive-validity-certificate construction to total verifiable refinements. It is useful for checking whether a search construction can separate intrinsic round budgets when changes of presentation are allowed. The empty input follows the published length-one resource convention.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definitions 1.1–1.2, pp.6–7. Generalization of the certified-replacement construction developed here: certificate completeness for all valid answers is replaced by soundness and totality of a refinement. This auxiliary construction is not asserted in the source.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.total_certified_refinement_resources {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
    (heff : {s | ∃ x y z, s = tup [x,y,z] ∧ V x y z} ∈ Delta i)
    (hsound : ∀ x y v, v.length = c.eval x.length → V x y v → R x y)
    (htotal : ∀ x, ∃ y v, v.length = c.eval x.length ∧ V x y v)
    (r q : ℕ → ℕ) (hr : PolyTimeLength r) (hq : PolyTimeLength q)
    (hrpos : ∀ n, 1 ≤ resource r n) (hqpos : ∀ n, 1 ≤ resource q n)
    (hevent : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ resource r n) : R ∈ ST i r q := by sorry
