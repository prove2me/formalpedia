-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_typicalSequenceMass
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.typicalSequenceMass
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:13:44.15761+00:00
-- url     : https://prove2.me/theorems/6bf1ab5d-decf-45d9-9660-6f4e002525ee
-- title:
--   §7.1 (ii), Appendix C: exponentially high typical mass
-- statement:
--   Let $P$ be a probability distribution on a finite nonempty alphabet $L$: $P_i\ge0$ and $\sum_iP_i=1$. Define $H(P)=-\sum_iP_i\log_2P_i$, with $0\log_20=0$. For $w\in L^n$, set $p_w=\prod_tP_{w_t}$ and $T_{\varepsilon,n}=\{w:2^{-n(H(P)+\varepsilon)}\le p_w\le2^{-n(H(P)-\varepsilon)}\}$. For each $\varepsilon>0$ there is a number $\psi>0$, depending on $P$ and $\varepsilon$ but independent of $n$, such that every positive integer $n$ satisfies
--
--   $$
--   \sum_{w\in T_{\varepsilon,n}}p_w>1-2e^{-n\psi}.
--   $$
--
--   Finite-alphabet IID sampling has exponentially high typical mass, including deterministic distributions.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 15, §7.1 (ii), Appendix C: exponentially high typical mass

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.15,21, §7.1(ii): a positive exponent chosen before every positive block length.
Deterministic distributions require no division by their zero information variance. -/
theorem typicalSequenceMass [Nonempty L] (P : L → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hsum : ∑ i, P i = 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ psi : ℝ, 0 < psi ∧ ∀ n : ℕ, 0 < n →
      1 - 2 * Real.exp (-(n : ℝ) * psi) < weakTypicalMass P epsilon n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
