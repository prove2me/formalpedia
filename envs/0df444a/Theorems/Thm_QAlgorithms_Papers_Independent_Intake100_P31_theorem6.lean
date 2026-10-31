-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem6
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:52:05.618121+00:00
-- url     : https://prove2.me/theorems/521f51fe-2db1-45e1-b85f-67cacc12b682
-- title:
--   Theorem 6: extension with bounded pair spectrum
-- statement:
--   For a binary code $C\le\mathbb F_2^n$, let $A_k(C)$ count its weight-$k$ codewords and put $\varepsilon_k(C)=A_k(C)2^{n-\dim C}/\binom nk$ and $\varepsilon(C)=\max_{1\le k\le n}\varepsilon_k(C)$. The permutation orbit is indexed by every permutation in $S_n$, including repetitions of identical codes. For $K\le L\le\mathbb F_2^n$, set $\varepsilon(L/K)=\max_{1\le k\le n}[\varepsilon_k(L)-(|K|/|L|)\varepsilon_k(K)]$. A dimension-$t$ universal pair family $(K_r,L_r)$ satisfies $K_r\le L_r$ and $\Pr_r[x\in L_r\setminus K_r]\le\varepsilon2^{t-n}$ for every nonzero $x$. For $n\ge1$, $t\le n$, and any $K$ with $\dim K\le t$, there exists $L$ such that
--
--   $$K\le L,\quad\dim L=t,\quad\varepsilon(L/K)\le n+1.$$
--
--   The dimension-feasibility hypothesis is required by the source's extension construction; the printed statement omits it.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 9, Theorem 6: extension with bounded pair spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.9, Theorem 6, with the omitted feasibility condition dim(small)≤t,
which the proof uses when choosing a dimension-t extended code. -/
theorem theorem6 {n t : ℕ} (hn : 0 < n) (htn : t ≤ n) (small : BinaryLinearCode n)
    (ht : Module.finrank (ZMod 2) small ≤ t) :
    ∃ large : BinaryLinearCode n, small ≤ large ∧ Module.finrank (ZMod 2) large = t ∧
      pairSpectrumParameter small large ≤ n + 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
