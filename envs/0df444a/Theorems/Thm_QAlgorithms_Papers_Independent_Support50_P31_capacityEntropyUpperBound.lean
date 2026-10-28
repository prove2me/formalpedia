-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_capacityEntropyUpperBound
-- name    : QAlgorithms.Papers.Independent.Support50.P31.capacityEntropyUpperBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:32:16.159842+00:00
-- url     : https://prove2.me/theorems/4b1c0a30-6e35-45b7-8d31-68859ca9b0af
-- title:
--   Universal one-step capacity upper bound
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving endomorphism on operators on a complex Hilbert space $H$ with finite dimension $d>0$. Let $C(\Phi)$ be the maximum of the Holevo information over all finite probability ensembles of density inputs, and let $\nu_H(\Phi)=\min_\rho H(\Phi(\rho))$, where $H(\sigma)=-\operatorname{Tr}(\sigma\log\sigma)$ uses natural logarithms and $0\log0=0$. Then
--   $$
--   C(\Phi)\le\log d-\nu_H(\Phi).
--   $$
--   The bound applies to every such channel, without a unitality or qubit assumption. It supplies the entropy-based upper bound used in the source's binary and depolarizing capacity arguments.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 9, §5, equation (19): one-step capacity bound

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

/-- PDF p.9, (19): universal one-step capacity bound, with no unitality assumption. -/
theorem capacityEntropyUpperBound {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (Phi : Superop I I) (hPhi : IsChannel Phi) :
    holevoQuantity Phi ≤ Real.log (Fintype.card I : ℝ) - nuH Phi := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
