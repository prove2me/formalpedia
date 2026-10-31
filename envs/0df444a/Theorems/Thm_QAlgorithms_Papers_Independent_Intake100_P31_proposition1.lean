-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_proposition1
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.proposition1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:50:34.191756+00:00
-- url     : https://prove2.me/theorems/44ec2386-f6a6-4697-8602-e50f0c642c4c
-- title:
--   Proposition 1: a universally bounded permutation family
-- statement:
--   For every $1\le t\le n$, there exists a dimension-$t$ binary code $C$ whose orbit under a uniformly sampled permutation satisfies
--
--   $$\forall x\ne0,\quad\Pr_{\sigma\in S_n}[x\in\sigma C]\le(n+1)2^{t-n}.$$
--
--   All permutations are retained, even when some produce identical codes. This supplies a bounded-universality deterministic orbit.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 9, Proposition 1: a universally bounded permutation family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.9, Proposition 1. -/
theorem proposition1 {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) (htn : t ≤ n) :
    ∃ C : BinaryLinearCode n, Module.finrank (ZMod 2) C = t ∧
      UniversalAt (permCode C) t (n + 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
