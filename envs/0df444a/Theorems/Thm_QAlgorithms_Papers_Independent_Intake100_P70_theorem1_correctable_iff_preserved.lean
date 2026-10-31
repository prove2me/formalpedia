-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_theorem1_correctable_iff_preserved
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.theorem1_correctable_iff_preserved
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:32:57.115778+00:00
-- url     : https://prove2.me/theorems/e8996514-e353-47b5-a96a-e73c8ffe8388
-- title:
--   Theorem 1: preservation iff correctability
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. Correctability means that some CPTP recovery makes $C$ noiseless, where noiselessness requires preservation under every probability mixture of nonnegative powers, including power zero. Then
--
--   $$C\text{ is correctable for }\mathcal E\iff C\text{ is preserved by }\mathcal E.$$
--
--   Moreover, writing $P=\operatorname{supp}C$, the support transpose map $\widehat{\mathcal E}_P(X)=P\mathcal E^\dagger(\mathcal E(P)^{-1/2}X\mathcal E(P)^{-1/2})P$ makes $C$ noiseless after $\mathcal E$. Inverses vanish on kernels; this formula is used on the reachable support, without asserting ambient trace preservation.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 7, Theorem 1: preservation iff correctability

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

/-- PDF pp.7,20–21, Theorem 1. CorrectableCode is Definition 9, not exact fixedness.
The proof's raw support-transpose composite makes C noiseless; it is not asserted
TP away from C's reachable support. -/
theorem theorem1_correctable_iff_preserved {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I)) (hC : IsCode C) :
    (CorrectableCode E C ↔ Preserved E C) ∧
      (Preserved E C → Noiseless (transposeRecovery E (codeSupport C) ∘ E) C) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
