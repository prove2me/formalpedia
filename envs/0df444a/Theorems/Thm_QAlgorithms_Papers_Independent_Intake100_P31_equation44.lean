-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_equation44
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.equation44
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:56:58.14692+00:00
-- url     : https://prove2.me/theorems/1603899b-1139-44d8-be06-3c5944723beb
-- title:
--   §V / Appendix B: corrected variational identity (44)
-- statement:
--   For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. For $R\in[0,1]$ and $p\in[0,1/2]$, with off-support Bernoulli divergence infinite,
--
--   $$\inf_{0\le q\le1/2}\bigl([1-h(q)-R]_++d(q\Vert p)\bigr)=E(R,p).$$
--
--   The maximum defining $E$ is over $s\in[0,1]$, correcting the printed $[0,1/2]$. This specialized identity is proved in Appendix B; the more general result is credited there to Csiszar and Korner.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 10, §V / Appendix B: corrected variational identity (44)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.10 (44), Appendix B pp.17--18: correct the printed s≤1/2 to s≤1.
At p=0,R=0 the left side is 1, whereas the printed right side is only 1/2. -/
theorem equation44 (R p : ℝ) (hR : R ∈ Set.Icc 0 1)
    (hp : p ∈ Set.Icc 0 (1 / 2)) :
    typeExponent R p = (gallagerExponent R p : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
