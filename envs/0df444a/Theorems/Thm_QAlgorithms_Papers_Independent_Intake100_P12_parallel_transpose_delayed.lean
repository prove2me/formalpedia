-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_parallel_transpose_delayed
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.parallel_transpose_delayed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:08:45.422227+00:00
-- url     : https://prove2.me/theorems/df1771cd-e030-47f2-8a15-c525173f158f
-- title:
--   Parallel transpose protocols can delay the input
-- statement:
--   Let $d\ge1$, $k\ge0$, and $p\in[0,1]$. If a fixed parallel $k$-slot instrument implements the transpose channel of every $U\in U(d)$ exactly with coefficient $p$, then there is a fixed delayed parallel instrument with
--
--   $$\mathcal L_{S_D}(C(U^{\otimes k}))=pC(U^{\mathsf T})\quad\text{for every }U.$$
--
--   The task and constant probability are preserved. The construction need not preserve the original failure branch or its behavior on nonunitary inputs.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 15, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.14–15, Lemma 2: a new delayed-input circuit preserves the task and p;
no preservation of the arbitrary original failure branch is asserted. -/
theorem parallel_transpose_delayed {d k : ℕ} (hd : 0 < d) (p : ℝ) :
    Attainable .parallel d k (targetChoi .transpose) p →
      DelayedAttainable d k (targetChoi .transpose) p := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
