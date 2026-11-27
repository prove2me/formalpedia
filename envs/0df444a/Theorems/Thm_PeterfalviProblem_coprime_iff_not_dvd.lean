-- Prove2me | Theorems.Thm_PeterfalviProblem_coprime_iff_not_dvd
-- name    : PeterfalviProblem.coprime_iff_not_dvd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:10:09.854671+00:00
-- url     : https://prove2.me/theorems/87478a63-7210-5983-b3c0-371d1e3ecc8f
-- title:
--   Peterfalvi Problem: coprime iff not dvd
-- statement:
--   The two forms of condition (A) agree: `(p^q - 1) / (p - 1)` is prime to `p - 1` exactly when
--   `q ∤ p - 1`. This is Lemma 8 of Glauberman–Norton and Remark (I) in Appendix C of
--   Bender–Glauberman.
--
--   The proof: `(p^q - 1) / (p - 1) = ∑_{i<q} p^i ≡ q` modulo `p - 1`, because `p ≡ 1`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L87-L101
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L87-L101

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
import Definitions.Def_PeterfalviProblem_Statement
import Definitions.Def_PeterfalviProblem_Basic_NormOneUnits
set_option autoImplicit false
open PeterfalviProblem
variable (p q : ℕ)

theorem PeterfalviProblem.coprime_iff_not_dvd (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ ¬ q ∣ p - 1 := by sorry
