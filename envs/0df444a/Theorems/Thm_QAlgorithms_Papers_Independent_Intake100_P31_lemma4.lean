-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_lemma4
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.lemma4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:48:31.840977+00:00
-- url     : https://prove2.me/theorems/dc272fb2-1ac3-479a-b70e-14f3e8ae580e
-- title:
--   Lemma 4: universality of a permutation orbit
-- statement:
--   For a binary code $C\le\mathbb F_2^n$, let $A_k(C)$ count its weight-$k$ codewords and put $\varepsilon_k(C)=A_k(C)2^{n-\dim C}/\binom nk$ and $\varepsilon(C)=\max_{1\le k\le n}\varepsilon_k(C)$. The permutation orbit is indexed by every permutation in $S_n$, including repetitions of identical codes. For every $n\ge1$ and every code $C$, its permuted family satisfies
--
--   $$\forall x\ne0,\quad\Pr_{\sigma\in S_n}[x\in\sigma C]\le\varepsilon(C)2^{\dim C-n}.$$
--
--   This converts a weight-spectrum estimate into a universality estimate.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 8, Lemma 4: universality of a permutation orbit

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.8, Lemma 4: all permutations are sampled uniformly, with multiplicity. -/
theorem lemma4 {n : ℕ} (hn : 0 < n) (C : BinaryLinearCode n) :
    UniversalAt (permCode C) (Module.finrank (ZMod 2) C) (spectrumParameter C) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
