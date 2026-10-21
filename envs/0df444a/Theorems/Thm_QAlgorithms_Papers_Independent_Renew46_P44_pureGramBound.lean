-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_pureGramBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.pureGramBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:26:37.254231+00:00
-- url     : https://prove2.me/theorems/89469af3-e8d1-4097-80d2-5fbc7cd1436f
-- title:
--   §III.1, (29),(31): Gram-matrix decoding bounds
-- statement:
--   Let $v_1,\ldots,v_M$ be unit vectors in a complex Hilbert space, where $M\ge1$, and let $\Gamma_{rs}=\langle v_r,v_s\rangle$ be their Gram matrix. Write $p_*(v)$ for the infimum uniform average discrimination error over bounded collective sub-POVMs and $I_M$ for the identity matrix. Linear dependence is allowed. Then
--
--   $$p_*(v)\le\frac2M\operatorname{Tr}(I_M-\sqrt\Gamma)
--   =\frac1M\operatorname{Tr}((I_M-\sqrt\Gamma)^2),$$
--
--   and
--
--   $$p_*(v)\le\frac1M\operatorname{Tr}((I_M-\Gamma)^2)
--   =\frac1M\sum_{r\ne s}|\langle v_r,v_s\rangle|^2.$$
--
--   These are the paper's square-root decoding and collision bounds; the generalized inverse underlying the rule is zero only on the kernel.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 10, §III.1, (29),(31): Gram-matrix decoding bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, (29),(31). Both traces in (29) are retained, the second
with the matrix square INSIDE the trace. Linear dependence is allowed. -/
theorem pureGramBound {I : Type} (M : ℕ) (hM : 0 < M)
    (v : Fin M → Hilbert I) (hv : ∀ k, ‖v k‖ = 1) :
    optimalCollectiveError (fun k => TC.rankOne (v k)) ≤
      ENNReal.ofReal (2 / (M : ℝ) * (Matrix.trace (1 - CFC.sqrt (pureSignalGram v))).re) ∧
    2 / (M : ℝ) * (Matrix.trace (1 - CFC.sqrt (pureSignalGram v))).re =
      (Matrix.trace ((1 - CFC.sqrt (pureSignalGram v)) ^ 2)).re / (M : ℝ) ∧
    optimalCollectiveError (fun k => TC.rankOne (v k)) ≤
      ENNReal.ofReal ((Matrix.trace ((1 - pureSignalGram v) ^ 2)).re / (M : ℝ)) ∧
    (Matrix.trace ((1 - pureSignalGram v) ^ 2)).re / (M : ℝ) =
      (∑ r : Fin M, ∑ s : Fin M, if r = s then 0 else
        ‖inner ℂ (v r) (v s)‖ ^ 2) / (M : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
