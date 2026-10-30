-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_invariant_densities_and_identity
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.invariant_densities_and_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:12:33.33354+00:00
-- url     : https://prove2.me/theorems/91e3fba3-07e4-4b9a-9ff2-ac3b6ac088e5
-- title:
--   Lemma 15: invariant densities are Choi states; normalized identity preservation
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. The normalized, reference-first Choi operator is $c_T=(\mathrm{id}_{d_1}\otimes T)(|\Omega\rangle\langle\Omega|)$, where $|\Omega\rangle=d_1^{-1/2}\sum_i|i,i\rangle$, with two input-sized factors before $T$ acts. Let $U$ be irreducible and let $\mathcal K$ be the actual commutant of $\overline U\otimes V$. Then
--
--   $$\mathcal K\cap\mathcal D(\mathcal H_1\otimes\mathcal H_2)=\{c_T:T\in\mathcal T_{UV}\}.$$
--
--   If $V$ is also irreducible, every such channel satisfies $T(I_{d_1}/d_1)=I_{d_2}/d_2$; when $d_1=d_2$, it satisfies $T(I)=I$. The normalized identity equality corrects the unrestricted rectangular unital assertion printed on page 7. This characterizes precisely which invariant states encode channels.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 7, Lemma 15: invariant densities are Choi states; normalized identity preservation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section General

variable {G I O : Type*} [Group G] [TopologicalSpace G]

variable [Fintype I] [DecidableEq I] [inputNonempty : Nonempty I]

variable [Fintype O] [DecidableEq O] [outputNonempty : Nonempty O]

include inputNonempty outputNonempty

/-- PDF pp.7--8, Lemma 15, corrected for rectangular channels: the proof gives
T(I/d1)=I/d2. The printed ordinary unital assertion needs d1=d2. -/
theorem invariant_densities_and_identity (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat) :
    (covariantTensorCommutant U.mat V.mat ∩ {rho | IsDensityMatrix rho} =
      choiSet (covariantChannels U.mat V.mat)) ∧
    (Irreducible V.mat → ∀ T ∈ covariantChannels U.mat V.mat,
      T ((Fintype.card I : ℂ)⁻¹ • 1) = (Fintype.card O : ℂ)⁻¹ • 1 ∧
      (Fintype.card I = Fintype.card O → T 1 = 1)) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
