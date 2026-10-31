-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_lemma6
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.lemma6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:03:10.724594+00:00
-- url     : https://prove2.me/theorems/5f494a40-3930-4b8c-aa6b-7ba66890ba35
-- title:
--   Appendix B, Lemma 6: tilted Bernoulli variational identity
-- statement:
--   For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Let $R\in[0,1]$, $p\in[0,1]$, and $R<1-h(p)$. For $\theta\in[0,1]$, let $p_\theta=p^\theta/(p^\theta+(1-p)^\theta)$ on nondegenerate support, with $p_\theta=0$ if $p=0$ and $p_\theta=1$ if $p=1$, also at $\theta=0$. Then
--
--   $$\inf_{0\le\theta\le1}\bigl(d(p_\theta\Vert p)+[1-h(p_\theta)-R]_+\bigr)=E(R,p).$$
--
--   At $p=1/2$, no nonnegative rate meets the strict capacity condition; the other parameters give nonvacuous instances. The proof's incorrect convexity wording is not an assumption.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 17, Appendix B, Lemma 6: tilted Bernoulli variational identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.17--18, Lemma 6: the tiltedBernoulli law preserves support, including theta=0.
The printed convexity claim in the proof is a sign error, not an assumption. -/
theorem lemma6 (R p : ℝ) (hR : R ∈ Set.Icc 0 1) (hp : p ∈ Set.Icc 0 1)
    (hcap : R < 1 - binEntropy2 p) :
    tiltedExponent R p = (gallagerExponent R p : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
