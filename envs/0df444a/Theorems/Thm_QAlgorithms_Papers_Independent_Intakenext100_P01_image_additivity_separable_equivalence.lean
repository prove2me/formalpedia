-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_image_additivity_separable_equivalence
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.image_additivity_separable_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:23:46.321589+00:00
-- url     : https://prove2.me/theorems/e1caa4a2-a85c-4457-b63a-b9d19ec0940e
-- title:
--   Equivalent physical descriptions of image additivity
-- statement:
--   Fix quantum channels $T_i:M_{d_i}(\mathbb C)\to M_{n_i}(\mathbb C)$ in positive finite dimensions. The following are equivalent:
--   $$\operatorname{Im}(T_1\otimes T_2)=\operatorname{conv}\{A\otimes B:A\in\operatorname{Im}T_1,\ B\in\operatorname{Im}T_2\};$$
--   for every unit vector $\psi\in\mathbb C^{d_1}\otimes\mathbb C^{d_2}$, there exists a separable density matrix $\rho_{\mathrm{sep}}$ on the input tensor product with
--   $$(T_1\otimes T_2)(\psi\psi^*)=(T_1\otimes T_2)(\rho_{\mathrm{sep}}).$$
--   Separable means a finite convex combination of product density matrices. The separable state may depend on $\psi$, and the tensor map is the physical linear action on all operators.
--
--   This records the equivalence explicitly asserted in Definition 6.1.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 10, Definition 6.1: equivalence of two physical characterizations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Definition 6.1(i)–(ii), PDF p.10: the explicitly asserted equivalence; the separable
input may depend on each unit pure input. The tensor map acts on every entangled matrix input. -/
theorem image_additivity_separable_equivalence {d1 d2 n1 n2 : ℕ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (T : Superop (Fin d1) (Fin n1)) (S : Superop (Fin d2) (Fin n2))
    (hT : IsChannel T) (hS : IsChannel S) :
    letI : Nonempty (Fin d1) := ⟨⟨0, hd1⟩⟩
    letI : Nonempty (Fin d2) := ⟨⟨0, hd2⟩⟩
    IsImageAdditive T S ↔
      ∀ x : EuclideanSpace ℂ (Fin d1 × Fin d2), ‖x‖ = 1 →
        ∃ A : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ,
          Entanglement.IsSeparableDensity A ∧
          tensorOnFunctions T S (pureDensity x) = tensorOnFunctions T S A := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
