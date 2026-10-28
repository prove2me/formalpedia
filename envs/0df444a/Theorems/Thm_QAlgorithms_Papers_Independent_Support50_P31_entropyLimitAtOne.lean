-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_entropyLimitAtOne
-- name    : QAlgorithms.Papers.Independent.Support50.P31.entropyLimitAtOne
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:25:25.294589+00:00
-- url     : https://prove2.me/theorems/82b2748c-c563-4efe-894c-75e03086bf58
-- title:
--   Minimum output entropy as a right trace-power limit
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving endomorphism on a nonzero finite-dimensional complex Hilbert space. For real $p>1$, set $M_p(\Phi)=\max_\rho\operatorname{Tr}(\Phi(\rho)^p)$, where the maximum is over all density inputs, and let $\nu_H(\Phi)=\min_\rho[-\operatorname{Tr}(\Phi(\rho)\log\Phi(\rho))]$, using natural logarithms and $0\log0=0$. Then
--   $$
--   \lim_{p\downarrow1}\frac{1-M_p(\Phi)}{p-1}=\nu_H(\Phi).
--   $$
--   This limit connects output Schatten purity with minimum output entropy; the right-hand approach excludes the zero denominator at $p=1$.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 4, §2, right limit of maximal output p-purity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF p.4: right limit of maximal trace-power quotient, in natural units. -/
theorem entropyLimitAtOne {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (Phi : Superop I I) (hPhi : IsChannel Phi) :
    Tendsto (fun p : ℝ => (1 - maxPower p Phi) / (p - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (nuH Phi)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
