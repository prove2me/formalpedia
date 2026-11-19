-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_certified_replacement_resources
-- name    : StudentTeacher976.Adaptivity.certified_replacement_resources
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T18:28:32.58901+00:00
-- url     : https://prove2.me/theorems/f405585a-7650-4c30-982f-48f0964645b7
-- title:
--   Positive validity certificates yield a two-round refutation presentation
-- statement:
--   Let $R$ be a total polynomially bounded search relation with a refutable presentation at level $i$. Suppose that $R$ also has exact-length positive certificates: there are a polynomial $c$ and a predicate $V$ decidable in $\Delta_{i+1}^p$ such that
--
--   $$
--   R(x,y)\quad\Longleftrightarrow\quad
--   \exists v\in\{0,1\}^{c(|x|)}\;V(x,y,v).
--   $$
--
--   Let $r,q$ be polynomial-time length functions. Suppose their effective round and query counts are positive at every length, and the round count is at least two at every sufficiently large length. Then
--
--   $$
--   R\in\mathrm{ST}^{\Sigma_i^p}[r,q].
--   $$
--
--   The membership permits a new faithful refutation presentation of the same underlying relation. Neither monotonicity nor unboundedness of $r$ is required; eventual availability of two rounds suffices. The empty input uses the published length-one resource convention. This isolates a reusable consequence of allowing alternative refutation presentations, with the raw input length and both resource functions preserved. It does not assert a round reduction for a fixed presentation.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definitions 1.1–1.2, pp.6–7. Certified-replacement construction derived here for the published relation-only presentation interface; this auxiliary lemma is not asserted in the source.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.certified_replacement_resources {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
    (heff : {s | ∃ x y z, s = tup [x,y,z] ∧ V x y z} ∈ Delta i)
    (hV : ∀ x y, R x y ↔ ∃ v, v.length = c.eval x.length ∧ V x y v)
    (r q : ℕ → ℕ) (hr : PolyTimeLength r) (hq : PolyTimeLength q)
    (hrpos : ∀ n, 1 ≤ resource r n) (hqpos : ∀ n, 1 ≤ resource q n)
    (hevent : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ resource r n) : R ∈ ST i r q := by sorry
