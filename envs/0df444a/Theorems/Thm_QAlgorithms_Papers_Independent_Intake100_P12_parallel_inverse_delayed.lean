-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_parallel_inverse_delayed
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.parallel_inverse_delayed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:12:45.259974+00:00
-- url     : https://prove2.me/theorems/4ef926f2-7e3c-4b4c-9509-a5ab461b0f4c
-- title:
--   Parallel inverse protocols can delay the input
-- statement:
--   Let $d\ge1$, $k\ge0$ and $p\in[0,1]$. If $p$ is attainable by a parallel universal exact inversion instrument, it is also attainable by a delayed parallel instrument:
--
--   $$\mathcal A_{\rm parallel\ inverse}(d,k)\subseteq\mathcal A_{\rm delayed\ parallel\ inverse}(d,k).$$
--
--   The new instrument is fixed independently of $U$ and retains constant coefficient $p$. Its arbitrary failure outputs need not equal those of the original protocol.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 18, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.18, Lemma 4: universal parallel inversion can have delayed input with
unchanged constant success probability. -/
theorem parallel_inverse_delayed {d k : ℕ} (hd : 0 < d) (p : ℝ) :
    Attainable .parallel d k (targetChoi .inverse) p →
      DelayedAttainable d k (targetChoi .inverse) p := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
