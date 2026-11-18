-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_good_pair_advice_cover
-- name    : StudentTeacher976.Adaptivity.good_pair_advice_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:43:56.56652+00:00
-- url     : https://prove2.me/theorems/9ab50b70-eef7-4335-9bdf-ca8c6373840e
-- title:
--   Polynomial good-pair cover for the advice construction
-- statement:
--   Fix a bounded witness presentation, admissible resources, and a normalized winning tuple student in the operational setup of Claim 3.1. Let $U$ be all positive $n$-bit inputs, and suppose $k=r(nk)$. There are a list of $(k-1)$-element subsets $S_j\subseteq U$ and a leftover set $E\subseteq U$ such that
--
--   $$
--   \ell\le k(n+1),\qquad |E|<k,
--   $$
--
--   and every positive input is covered:
--
--   $$
--   x\in U\quad\Longrightarrow\quad
--   x\in E\ \lor\ \exists j<\ell:\bigl(x\in S_j\ \lor\ (S_j,x)\text{ is good}\bigr).
--   $$
--
--   Goodness refers to the actual fixed-teacher trace of the published student. This is the finite covering result used to assemble polynomial advice on pp.20–21. It keeps the individual sets so that the deciding simulation can use their witnesses.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 pp.20–21 (good-pair counting and Algorithm 1), Appendix A pp.39–40; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Teacher

namespace StudentTeacher976.Adaptivity

theorem good_pair_advice_cover (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (n k : ℕ) (hsize : k = resource r (n * k))
    (f : TupleStudent) (hf : UniformTupleStudent i f)
    (hshape : TupleStudentShape W n k (resource q (n * k)) f)
    (hsolve : TupleStudentWins W n k (resource q (n * k)) (normalize W f))
    (U : Finset Word) (hU : ∀ x, x ∈ U ↔ x ∈ positiveInputs W n) :
    ∃ A : List (Finset Word), ∃ R : Finset Word,
      A.length ≤ k * (n + 1) ∧
      (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧ R.card < k ∧
      ∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨
        GoodPair W n k (resource q (n * k)) f S x := by sorry

end StudentTeacher976.Adaptivity
