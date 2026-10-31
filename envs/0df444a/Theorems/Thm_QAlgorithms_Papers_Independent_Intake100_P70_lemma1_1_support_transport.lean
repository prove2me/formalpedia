-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma1_1_support_transport
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma1_1_support_transport
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:39:13.536839+00:00
-- url     : https://prove2.me/theorems/9b8b556b-0cad-42a0-a453-1f4378c8f097
-- title:
--   Lemma 1.1: support transport under a CP map
-- statement:
--   Let $\mathcal E:B(H)\to B(H^{\prime})$ be complex-linear and completely positive on nonzero finite-dimensional spaces. It need not preserve trace. If $X_0\ge0$, $P=\operatorname{supp}X_0$, $Q=\operatorname{supp}\mathcal E(X_0)$, and $X$ is any operator with $PXP=X$, then
--
--   $$Q\mathcal E(X)Q=\mathcal E(X).$$
--
--   Both-sided support includes non-Hermitian operators. At $X_0=0$, the supported input operator must be zero.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 21, Lemma 1.1: support transport under a CP map

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.21, Lemma 1.1. Arbitrary CP linear maps, no TP assumption;
X may be non-Hermitian. At X0=0 both corners reduce to zero. -/
theorem lemma1_1_support_transport {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Op I →ₗ[ℂ] Op J) (hE : QAlgorithms.Entanglement.IsCompletelyPositive E)
    (X0 X : Op I) (h0 : X0.PosSemidef) (hX : CornerSupported (supportProjector X0) X) :
    CornerSupported (supportProjector (E X0)) (E X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
