-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_proposition2
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.proposition2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:52:36.530115+00:00
-- url     : https://prove2.me/theorems/5029d2f8-cab7-4913-8418-dec5677becb1
-- title:
--   Proposition 2: permutation-universal extended pairs
-- statement:
--   For $K\le L\le\mathbb F_2^n$, set $\varepsilon(L/K)=\max_{1\le k\le n}[\varepsilon_k(L)-(|K|/|L|)\varepsilon_k(K)]$. A dimension-$t$ universal pair family $(K_r,L_r)$ satisfies $K_r\le L_r$ and $\Pr_r[x\in L_r\setminus K_r]\le\varepsilon2^{t-n}$ for every nonzero $x$. Let $1\le t\le n$ and fix $K$ with $\dim K\le t$. There exists $L\ge K$ of dimension $t$ for which
--
--   $$\Pr_{\sigma\in S_n}[x\in\sigma L\setminus\sigma K]\le(n+1)2^{t-n}\qquad(x\ne0).$$
--
--   The same permutation acts on both codes. The stated feasibility condition repairs the printed omission.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 9, Proposition 2: permutation-universal extended pairs

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.9, Proposition 2, corrected dimension feasibility as in Theorem 6. -/
theorem proposition2 {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) (htn : t ≤ n)
    (small : BinaryLinearCode n) (hd : Module.finrank (ZMod 2) small ≤ t) :
    ∃ large : BinaryLinearCode n, small ≤ large ∧ Module.finrank (ZMod 2) large = t ∧
      PairUniversalAt (permCode small) (permCode large) t (n + 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
