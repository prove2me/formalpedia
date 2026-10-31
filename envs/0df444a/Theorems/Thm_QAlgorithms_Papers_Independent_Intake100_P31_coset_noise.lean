-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_coset_noise
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.coset_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:58:22.841364+00:00
-- url     : https://prove2.me/theorems/e047d628-9e68-4666-8a33-8955bb2c937c
-- title:
--   §V, equation (46): arbitrary-noise bound for coset coding
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. Fix an inner code $K$ and an extended-code family $L_r\ge K$ with maximum dimension $t_{\max}$. Suppose $\varepsilon\ge1$ and $\Pr_r[x\in L_r]\le\varepsilon2^{t_{\max}-n}$ for every $x\notin K$. Put $R=t_{\max}/n$. Then
--
--   $$\mathbb E_r P_e(L_r/K)\le\varepsilon\sum_{k=0}^n\widehat P(k)F_R(k).$$
--
--   Each quotient message is uniform, and the transmitted word is uniform within its coset. The zero-weight term is retained as printed.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 11, §V, equation (46): arbitrary-noise bound for coset coding

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.11 (46): fixed inner code and arbitrary seed-independent additive law. -/
theorem coset_noise {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (small : BinaryLinearCode n) (large : I → BinaryLinearCode n) (eps : ℝ) (heps : 1 ≤ eps)
    (hu : ExtUniversalAt small large (maxDim large) eps) (P : ErrorLaw n) :
    avg (fun r => cosetWordError small (large r) P.mass) ≤
      noiseBound P.mass ((maxDim large : ℝ) / n) eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
