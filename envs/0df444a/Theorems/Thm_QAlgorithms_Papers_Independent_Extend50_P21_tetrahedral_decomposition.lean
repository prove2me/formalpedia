-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_tetrahedral_decomposition
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.tetrahedral_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:17:16.854146+00:00
-- url     : https://prove2.me/theorems/c286bd55-352b-42cf-9756-7cef8e66a3ce
-- title:
--   Example 23 / Eq. (3.1): tetrahedral tensor decomposition
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $A_4$ act by coordinate permutations on $H=\{a\in\mathbb C^4:\sum_i a_i=0\}$, and denote this real three-dimensional irreducible representation by $\vartheta$. Let $K_4$ be the Klein subgroup, $c=(123)$, $\zeta=e^{2\pi i/3}$, and $\phi_j(c^kK_4)=\zeta^{jk}$ for $j=0,1,2$. There is a physical unitary decomposition
--
--   $$\vartheta\otimes\vartheta\simeq\phi_0\oplus\phi_1\oplus\phi_2\oplus(\vartheta\otimes I_2).$$
--
--   The same unitary transports the actual commutant to $\mathbb C\oplus\mathbb C\oplus\mathbb C\oplus(I_3\otimes M_2(\mathbb C))$. The corresponding Choi set is not a polytope. Concrete real orthonormal coordinates for $H$ and its permutation action are constructed, retaining the physical representation rather than just abstract block sizes. The background identification of the irreducibles is attributed to [16, §2.3].
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 12, Example 23 / Eq. (3.1): tetrahedral tensor decomposition

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

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P21.tetraTopology

/-- PDF pp.12--13, Example 23 and Eq.(3.1): the physical permutation
representation, its five irreducible copies (four distinct types), transported
covariantTensorCommutant, and the non-polytope consequence. -/
theorem tetrahedral_decomposition :
    tetraBasisᴴ * tetraBasis = 1 ∧
    tetraBasis * tetraBasisᴴ = 1 - (1 / 4 : ℂ) • (Matrix.of fun _ _ : Fin 4 => 1) ∧
    (∀ g i j, (tetraMatrices g i j).im = 0) ∧
    (∃ theta : ContinuousUnitaryRep (alternatingGroup (Fin 4)) (Fin 3),
      (∀ g, theta.mat g = tetraMatrices g) ∧ Irreducible theta.mat) ∧
    (∀ j : Fin 3, ∃ phi : ContinuousUnitaryRep (alternatingGroup (Fin 4)) (Fin 1),
      (∀ g, phi.mat g 0 0 = tetraCharacter j g) ∧ Irreducible phi.mat) ∧
    (∃ W : Matrix (Fin 3 × Fin 3) (Fin 3 ⊕ (Fin 3 × Fin 2)) ℂ,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (∀ g, Matrix.kronecker (tetraMatrices g) (tetraMatrices g) * W = W * tetraBlocks g) ∧
      covariantTensorCommutant tetraMatrices tetraMatrices =
        {X | ∃ scalar : Fin 3 → ℂ, ∃ B : Matrix (Fin 2) (Fin 2) ℂ,
          X = W * Matrix.fromBlocks (Matrix.diagonal scalar) 0 0
            (Matrix.kronecker (1 : Matrix (Fin 3) (Fin 3) ℂ) B) * Wᴴ}) ∧
    ¬ Polytope (choiSet tetraClass) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P21

end
