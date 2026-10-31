-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_corollary3
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.corollary3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:55:09.519011+00:00
-- url     : https://prove2.me/theorems/14cc1f5d-433b-4609-a443-148a1397726e
-- title:
--   Corollary 3: reliability exponent and positivity
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. For maximum-dimension universality with $\varepsilon>0$, iid BSC parameter $p\in[0,1]$, and $R=t_{\max}/n$, the ML word error satisfies
--
--   $$\mathbb E_r P_e(C_r)\le2^{-nE(R,p)}\max\{\varepsilon,1\},\qquad R<1-h(p)\Longrightarrow E(R,p)>0.$$
--
--   This retains both the ensemble bound and its positivity regime.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 10, Corollary 3: reliability exponent and positivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.10, Corollary 3: gallagerExponent bound and the strictly positive regime. -/
theorem corollary3 {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (C : I → BinaryLinearCode n) (eps : ℝ) (heps : 0 < eps)
    (hu : UniversalAt C (maxDim C) eps) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    avg (fun r => cosetWordError ⊥ (C r) (bsc p)) ≤
      (2 : ℝ) ^ (-(n : ℝ) * gallagerExponent ((maxDim C : ℝ) / n) p) * max eps 1 ∧
    (((maxDim C : ℝ) / n) < 1 - binEntropy2 p →
      0 < gallagerExponent ((maxDim C : ℝ) / n) p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
