-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem7
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:54:35.10659+00:00
-- url     : https://prove2.me/theorems/d920751e-7812-4ca2-818a-16f21772824d
-- title:
--   Theorem 7: iid ensemble Gallager error bound
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Suppose maximum-dimension universality holds with $\varepsilon>0$. For iid Bernoulli noise with parameter $p\in[0,1]$ and rate $R=t_{\max}/n$,
--
--   $$\mathbb E_r P_e(C_r)\le\min_{0\le s\le1}\varepsilon^s2^{-n[-sR+E_0(s,p)]}.$$
--
--   The factor $\varepsilon^s$ remains inside the minimum. The decoder is ML for the actual parameter, including both deterministic endpoints and $p>1/2$.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 10, Theorem 7: iid ensemble Gallager error bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.10, Theorem 7: iid ML bound for all p in [0,1], including p>1/2. -/
theorem theorem7 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (C : I → BinaryLinearCode n) (eps : ℝ) (heps : 0 < eps)
    (hu : UniversalAt C (maxDim C) eps) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    avg (fun r => cosetWordError ⊥ (C r) (bsc p)) ≤
      gallagerBound n ((maxDim C : ℝ) / n) p eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
