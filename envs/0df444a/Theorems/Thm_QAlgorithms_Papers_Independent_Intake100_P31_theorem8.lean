-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem8
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:59:10.987988+00:00
-- url     : https://prove2.me/theorems/975e8c5c-481e-479a-a1bc-190a04642c87
-- title:
--   Theorem 8: Gallager bounds for extended codes and full code-pair ensembles
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. For $K\le L\le\mathbb F_2^n$, set $\varepsilon(L/K)=\max_{1\le k\le n}[\varepsilon_k(L)-(|K|/|L|)\varepsilon_k(K)]$. A dimension-$t$ universal pair family $(K_r,L_r)$ satisfies $K_r\le L_r$ and $\Pr_r[x\in L_r\setminus K_r]\le\varepsilon2^{t-n}$ for every nonzero $x$. For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Let both codes $K_r\le L_r$ vary on the same seed, set $t_{\max}=\max_r\dim L_r$ and $R=t_{\max}/n$, and assume dimension-$t_{\max}$ pair universality with $\varepsilon>0$. For iid BSC noise of parameter $p\in[0,1]$,
--
--   $$\mathbb E_rP_e(L_r/K_r)\le\min_{0\le s\le1}\varepsilon^s2^{-n[-sR+E_0(s,p)]},\qquad\mathbb E_rP_e(L_r/K_r)\le2^{-nE(R,p)}\max\{\varepsilon,1\}.$$
--
--   This includes the fixed-inner extended-code case and preserves the full pair-ensemble conclusion.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 11, Theorem 8: Gallager bounds for extended codes and full code-pair ensembles

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.11, Theorem 8: complete pair ensemble, encompassing the fixed-inner
specialization. Appendix A uses competitors in large minus small. -/
theorem theorem8 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (small large : I → BinaryLinearCode n) (eps : ℝ) (heps : 0 < eps)
    (hu : PairUniversalAt small large (maxDim large) eps)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    avg (fun r => cosetWordError (small r) (large r) (bsc p)) ≤
      gallagerBound n ((maxDim large : ℝ) / n) p eps ∧
    avg (fun r => cosetWordError (small r) (large r) (bsc p)) ≤
      (2 : ℝ) ^ (-(n : ℝ) * gallagerExponent ((maxDim large : ℝ) / n) p) * max eps 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
