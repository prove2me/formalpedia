-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_proposition3
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.proposition3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:53:20.427875+00:00
-- url     : https://prove2.me/theorems/f3508818-434e-400a-8466-36044f54d243
-- title:
--   Proposition 3: permutation-dual-universal subcode pairs
-- statement:
--   For $K\le L\le\mathbb F_2^n$, set $\varepsilon(L/K)=\max_{1\le k\le n}[\varepsilon_k(L)-(|K|/|L|)\varepsilon_k(K)]$. A dimension-$t$ universal pair family $(K_r,L_r)$ satisfies $K_r\le L_r$ and $\Pr_r[x\in L_r\setminus K_r]\le\varepsilon2^{t-n}$ for every nonzero $x$. Let $1\le t\le n$ and fix $L$ with $t\le\dim L$. There exists a dimension-$t$ subcode $K\le L$ such that
--
--   $$\Pr_{\sigma\in S_n}[x\in(\sigma K)^\perp\setminus(\sigma L)^\perp]\le(n+1)2^{-t}\qquad(x\ne0).$$
--
--   Thus the permuted original pair is almost dual universal. The dimension-feasibility condition repairs the printed omission.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 9, Proposition 3: permutation-dual-universal subcode pairs

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.9, Proposition 3, corrected feasibility t≤dim(large). -/
theorem proposition3 {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) (htn : t ≤ n)
    (large : BinaryLinearCode n) (hd : t ≤ Module.finrank (ZMod 2) large) :
    ∃ small : BinaryLinearCode n, small ≤ large ∧ Module.finrank (ZMod 2) small = t ∧
      PairUniversalAt (fun s => binDual (permCode large s))
        (fun s => binDual (permCode small s)) (n - t) (n + 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
