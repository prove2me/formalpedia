-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_uniform_refutation_translation_transfer
-- name    : StudentTeacher976.Adaptivity.uniform_refutation_translation_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:24:09.853862+00:00
-- url     : https://prove2.me/theorems/88ab63f1-355e-4bec-8e0a-3d32bdcc1736
-- title:
--   Uniform students transfer along efficient refutation translations
-- statement:
--   Let $P$ and $Q$ be refutable presentations of the same search relation at hierarchy level $i$. Let $r$ be any round function and $q$ a polynomial-time query function. Suppose a function $\psi(x,y,z)$ is computable in $\mathrm{FP}^{\Sigma_i^p}$ on the encoded triple, and for every $P$-certificate $z$ of its prescribed length,
--
--   $$
--   |\psi(x,y,z)|=b_Q(|x|),\qquad
--   Q(x,y,\psi(x,y,z))\Longrightarrow P(x,y,z).
--   $$
--
--   Here $P(x,y,z)$ and $Q(x,y,w)$ denote the presentations' Boolean success tests, not the underlying binary relation. Then
--
--   $$
--   Q\text{ has a uniform winning }(r,q)\text{ student}
--   \Longrightarrow
--   P\text{ has a uniform winning }(r,q)\text{ student}.
--   $$
--
--   The translated student processes only earlier reply batches, so it preserves the round and parallel-query budgets exactly. This interface makes the computational requirement on a change of presentation explicit.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definition 1.2, p.7; causal composition interface for the published uniform-student model.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.uniform_refutation_translation_transfer {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (hq : PolyTimeLength q) (ψ : Word → Word → Word → Word)
    (heff : ∃ F : Word → Word,InFP i F ∧ ∀ x y z,F (tup [x,y,z])=ψ x y z)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x y z) → P.test x y z)
    (g : Student) (hg : UniformStudent i g) (hshape : StudentShape Q r q g)
    (hwin : StudentWins Q r q g) :
    ∃ f : Student,UniformStudent i f ∧ StudentShape P r q f ∧ StudentWins P r q f := by sorry
