-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem5
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:49:48.185934+00:00
-- url     : https://prove2.me/theorems/160709bf-caad-4a39-b19a-82dc99493b9c
-- title:
--   Theorem 5: a code with bounded weight spectrum
-- statement:
--   For a binary code $C\le\mathbb F_2^n$, let $A_k(C)$ count its weight-$k$ codewords and put $\varepsilon_k(C)=A_k(C)2^{n-\dim C}/\binom nk$ and $\varepsilon(C)=\max_{1\le k\le n}\varepsilon_k(C)$. The permutation orbit is indexed by every permutation in $S_n$, including repetitions of identical codes. For integers $1\le t\le n$, there exists a code $C$ such that
--
--   $$\dim C=t,\qquad\varepsilon(C)\le n+1.$$
--
--   This is a simultaneous bound on every nonzero weight, with the code selected before the weight.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 8, Theorem 5: a code with bounded weight spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.8--9, Theorem 5. -/
theorem theorem5 {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) (htn : t ≤ n) :
    ∃ C : BinaryLinearCode n, Module.finrank (ZMod 2) C = t ∧ spectrumParameter C ≤ n + 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
