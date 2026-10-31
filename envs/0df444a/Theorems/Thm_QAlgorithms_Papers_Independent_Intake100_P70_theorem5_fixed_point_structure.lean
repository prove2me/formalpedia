-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_theorem5_fixed_point_structure
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.theorem5_fixed_point_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:36:25.446342+00:00
-- url     : https://prove2.me/theorems/d844451b-c577-4157-bb0e-d4e66307aaa7
-- title:
--   Theorem 5: full four-part fixed-point structure theorem
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $P_0$ be the joint support of all fixed operators and $\mathcal E_0$ the restriction to $B(P_0)$. All four assertions hold: (i) $P_0$ is invariant; (ii) $A=\operatorname{Fix}(\mathcal E_0^\dagger)$ is a concrete matrix star algebra on that corner; (iii) in orthogonal coordinates $P_0=\bigoplus_k(A_k\otimes B_k)$ there are positive factors $\tau_k$ of trace $\dim B_k$ with
--
--   $$A=\bigoplus_kM_{A_k}\otimes I_{B_k},\qquad\operatorname{Fix}(\mathcal E)=\bigoplus_kM_{A_k}\otimes\tau_k;$$
--
--   (iv) compression $Y\mapsto P_0YP_0$ maps $\operatorname{Fix}(\mathcal E^\dagger)$ bijectively onto $A$. The orthogonal physical complement carries zero in the displayed algebraic spaces. This simultaneously describes fixed states and fixed observables.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 9, Theorem 5: full four-part fixed-point structure theorem

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

/-- PDF pp.9,22–25, Theorem 5, all four parts. The algebra is on B(P0),
not a TP restriction on all of B(H). Distortion factors have trace dim(B_k)
for the unnormalized identities in Definition 10. Compression of full adjoint
fixed points is a bijection onto the computed corner algebra. -/
theorem theorem5_fixed_point_structure {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    CornerInvariant E (fixedSupport E) ∧
    IsMatrixAlgebra (fixedSupport E) (cornerAlgebra E) ∧
    (∃ B : BlockModel I, IsFixedDecomposition E B ∧
      ∃ tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k)),
        B.DistortionFactors tau ∧ fixedOperators E = B.blockSpace tau) ∧
    (∀ X ∈ fixedOperators (channelAdjoint E),
      fixedSupport E * X * fixedSupport E ∈ cornerAlgebra E) ∧
    (∀ X ∈ cornerAlgebra E, ∃! Y : Op I,
      Y ∈ fixedOperators (channelAdjoint E) ∧ fixedSupport E * Y * fixedSupport E = X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
