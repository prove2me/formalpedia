-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_lemma5
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.lemma5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:51:31.02983+00:00
-- url     : https://prove2.me/theorems/d692ac16-1743-4227-9748-5c32712ca90e
-- title:
--   Lemma 5: permutation families of nested pairs
-- statement:
--   For a binary code $C\le\mathbb F_2^n$, let $A_k(C)$ count its weight-$k$ codewords and put $\varepsilon_k(C)=A_k(C)2^{n-\dim C}/\binom nk$ and $\varepsilon(C)=\max_{1\le k\le n}\varepsilon_k(C)$. The permutation orbit is indexed by every permutation in $S_n$, including repetitions of identical codes. For $K\le L\le\mathbb F_2^n$, set $\varepsilon(L/K)=\max_{1\le k\le n}[\varepsilon_k(L)-(|K|/|L|)\varepsilon_k(K)]$. A dimension-$t$ universal pair family $(K_r,L_r)$ satisfies $K_r\le L_r$ and $\Pr_r[x\in L_r\setminus K_r]\le\varepsilon2^{t-n}$ for every nonzero $x$. For $n\ge1$ and $K\le L$, applying the same uniformly sampled permutation to both codes gives
--
--   $$\Pr_{\sigma\in S_n}[x\in\sigma L\setminus\sigma K]\le\varepsilon(L/K)2^{\dim L-n}\qquad(x\ne0).$$
--
--   The maximum in the parameter encloses the entire difference.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 9, Lemma 5: permutation families of nested pairs

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.9, Lemma 5: the SAME permutation acts on both codes. -/
theorem lemma5 {n : ℕ} (hn : 0 < n) (small large : BinaryLinearCode n) (h : small ≤ large) :
    PairUniversalAt (permCode small) (permCode large) (Module.finrank (ZMod 2) large)
      (pairSpectrumParameter small large) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
