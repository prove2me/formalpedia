-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_advice_implementation
-- name    : StudentTeacher976.Adaptivity.auxiliary_advice_implementation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-17T23:43:20.686907+00:00
-- url     : https://prove2.me/theorems/734fc660-e17e-4b3e-87fa-4ac4a0f322a5
-- title:
--   Implementing the lower-game polynomial-advice decision procedure
-- statement:
--   Let $L$ have a bounded existential $\Delta_{i+1}^p$ witness presentation, and let $r,q$ satisfy the resource assumptions of Theorem 1.4. Assume the raw auxiliary relation belongs to the lower-round game class. Supply the two finite ingredients of the source's advice construction:
--
--   1. One exponent $d$ bounds positive fixed points at every positive decision length:
--
--   $$
--   \forall n>0\;\exists k:\quad 0<k\le(n+1)^d,\qquad k=r(nk).
--   $$
--
--   2. For every fixed-length operational normalized tuple student satisfying the source's shape and winning premises, a good-pair cover of all positive $n$-bit inputs exists using at most $k(n+1)$ sets of size $k-1$ and fewer than $k$ leftover points, with the actual fixed teacher.
--
--   Then the source's advice-and-simulation construction can be implemented by one finite oracle machine with one polynomial clock and length-uniform polynomial advice:
--
--   $$
--   L\in\Delta_{i+1}^p/\mathrm{poly}.
--   $$
--
--   This isolates the operational part of Algorithm 1 on p.21 after input-size existence and finite covering have been supplied. It includes the interface from lower membership of the underlying relation to the simulations used by the algorithm; no certificate translation or machine simulation is assumed implicitly.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §3.1 pp.20–21 (good-pair counting and Algorithm 1), Appendix A pp.39–40; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion
import Definitions.Def_StudentTeacher976_Adaptivity_Teacher

namespace StudentTeacher976.Adaptivity

theorem auxiliary_advice_implementation (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hgame : auxiliaryRelation W r ∈ ST i r q)
    (hpoints : ∃ d : ℕ, ∀ n : ℕ, 0 < n → ∃ k : ℕ,
      0 < k ∧ k ≤ (n + 1) ^ d ∧ k = r (n * k))
    (hcovers : ∀ (n k : ℕ) (hsize : k = resource r (n * k))
    (f : TupleStudent) (hf : UniformTupleStudent i f)
    (hshape : TupleStudentShape W n k (resource q (n * k)) f)
    (hsolve : TupleStudentWins W n k (resource q (n * k)) (normalize W f))
    (U : Finset Word) (hU : ∀ x, x ∈ U ↔ x ∈ positiveInputs W n),
    ∃ A : List (Finset Word), ∃ R : Finset Word,
      A.length ≤ k * (n + 1) ∧
      (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧ R.card < k ∧
      ∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨
        GoodPair W n k (resource q (n * k)) f S x) :
    L ∈ DeltaPoly i := by sorry

end StudentTeacher976.Adaptivity
