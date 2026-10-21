-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_entropyWeakLowerSemicontinuity
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.entropyWeakLowerSemicontinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:51:29.555991+00:00
-- url     : https://prove2.me/theorems/a98d0aab-5f71-459c-9b1e-f56cc08bf39a
-- title:
--   §II Lemma: weak lower semicontinuity of entropy
-- statement:
--   Let $A_l$ and $A$ be normalized positive trace-class density operators on the same arbitrary complex Hilbert space. Suppose $\langle u,A_lv\rangle\to\langle u,Av\rangle$ for every pair of Hilbert vectors $u,v$. With von Neumann entropy in nats taking values in $[0,\infty]$,
--
--   $$H(A)\le\liminf_{l\to\infty}H(A_l).$$
--
--   No finite-entropy assumption or uniform entropy bound is required. The paper reproduces this well-known lemma with a proof sketch.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 7, §II Lemma: weak lower semicontinuity of entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma, PDF p.7: weak lower semicontinuity of entropy. Reproduced as a
well-known fact with proof sketch in the source. Infinite entropy remains
representable; there is no condition (8) or dimension restriction. -/
theorem entropyWeakLowerSemicontinuity {I : Type} (X : ℕ → constrainedCqState I) (Y : constrainedCqState I)
    (hweak : ∀ u v : Hilbert I,
      Tendsto (fun l => inner (𝕜 := ℂ) u ((X l).val v)) atTop
        (𝓝 (inner (𝕜 := ℂ) u (Y.val v)))) :
    constrainedCqEntropy Y.val ≤ Filter.liminf (fun l => constrainedCqEntropy (X l).val) atTop := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
