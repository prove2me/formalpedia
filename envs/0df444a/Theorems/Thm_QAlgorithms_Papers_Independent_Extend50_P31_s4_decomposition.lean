-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_s4_decomposition
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.s4_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:00:03.048813+00:00
-- url     : https://prove2.me/theorems/589138da-e495-4c94-aafd-419f1a0684a7
-- title:
--   Section 8.4, Eq.(145): S(4) triplet tensor decomposition
-- statement:
--   Let $U$ be the $S_4$ triplet of partition $(3,1)$, identified by $\chi_U(g)=\#\operatorname{Fix}(g)-1$. There exist unitary irreducible summands of partitions $(2,2)$ and $(2,1,1)$, identified by their characters, and an invertible intertwiner implementing
--
--   $$
--   U\otimes\overline U\simeq\mathrm{id}\oplus\varphi^{(3,1)}\oplus\varphi^{(2,2)}\oplus\varphi^{(2,1,1)},\qquad\dim_{\mathbb C}\operatorname{Int}_{S_4}(U\otimes\overline U)=4.
--   $$
--
--   The other characters are $\chi_{(2,2)}(g)=(f(g)^2+f(g^2))/2-2f(g)$ and $\chi_{(2,1,1)}(g)=\operatorname{sgn}(g)(f(g)-1)$, where $f(g)=\#\operatorname{Fix}(g)$. The displayed dimensions sum to nine and the sign representation does not occur. Equivalent realizations give the same decomposition.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 28, Section 8.4, Eq.(145): S(4) triplet tensor decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.28 Eq.(145), independently of the inconsistent entrywise matrices. -/
theorem s4_decomposition (U : UnitaryIrrep (Equiv.Perm (Fin 4)) 3)
    (hU : ∀ g, character U g = s4StandardCharacter g) :
    (∃ V : UnitaryIrrep (Equiv.Perm (Fin 4)) 2,
      ∃ W : UnitaryIrrep (Equiv.Perm (Fin 4)) 3,
        (∀ g, character V g = s4DoubletCharacter g) ∧
        (∀ g, character W g = s4TwistCharacter g) ∧ S4TripletDecomposition U V W) ∧
    Module.finrank ℂ (representationCommutant (tensorConjugate U)) = 4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
