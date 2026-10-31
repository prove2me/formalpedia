-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_general_noise
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.general_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:53:53.79692+00:00
-- url     : https://prove2.me/theorems/8e3643fc-7ecd-421d-887d-c1f4f1ddc8a5
-- title:
--   §V, equations (37)–(38): error bounds for an arbitrary additive law
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. Assume maximum-dimension universality with $\varepsilon\ge1$ and put $R=t_{\max}/n$. Let $B(x,C)$ indicate the existence of a nonzero $c\in C$ with $|x-c|\le|x|$, conservatively treating ties as failures. Then
--
--   $$\mathbb E_r B(x,C_r)\le\varepsilon F_R(|x|),\qquad\mathbb E_r P_e(C_r)\le\varepsilon\sum_{k=1}^n\widehat P(k)F_R(k).$$
--
--   The translated Hamming ball is essential. ML error is bounded above by the Hamming estimate; it is not identified with it for an arbitrary noise law.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 10, §V, equations (37)–(38): error bounds for an arbitrary additive law

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.9--10 (35)--(38), corrected translated Hamming ball and ML inequality.
The conservative failure indicator includes every tie, so its law also bounds ML error. -/
theorem general_noise {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (C : I → BinaryLinearCode n) (eps : ℝ) (heps : 1 ≤ eps)
    (hu : UniversalAt C (maxDim C) eps) (P : ErrorLaw n) :
    (∀ x : BinaryBlock n, avg (fun r => hammingBad (C r) x) ≤ eps *
      (2 : ℝ) ^ (-(n : ℝ) * max (1 - binEntropy2 (min ((wt x : ℝ) / n) (1 / 2)) -
        (maxDim C : ℝ) / n) 0)) ∧
    avg (fun r => cosetWordError ⊥ (C r) P.mass) ≤
      wordNoiseBound P.mass ((maxDim C : ℝ) / n) eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
