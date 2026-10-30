-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_highWignerAffineIsotropic
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.highWignerAffineIsotropic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:31:24.554828+00:00
-- url     : https://prove2.me/theorems/cb070b06-ffc2-4030-a638-f790370fcce5
-- title:
--   High Wigner values lie in an affine isotropic submodule
-- statement:
--   Let $d\geq2$ be odd and $\psi$ a normalized pure $n$-qudit state. Let $w_\psi$ be its Wigner function with normalization $w_\psi(x)=d^{-n}\operatorname{tr}(\psi A_x)$. The high-value set is contained in a translate $a+M$ of a $\mathbb Z_d$-submodule $M$ on which the symplectic bracket vanishes identically. The high-value set may be empty.
--
--   $$
--   \{x:w_\psi(x)>d^{-n}\sqrt{1-1/(2d^2)}\}\subseteq a+M.
--   $$
--
--   This gives the source's high wigner values lie in an affine isotropic submodule in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 60, corollary-8.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.60, Corollary 8.3: containment in an affine isotropic Z_d-submodule, including composite d. -/
theorem highWignerAffineIsotropic (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (hodd : Odd d)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) (hv : ‖v‖ = 1) :
    ∃ a : DiscretePhaseSpace d n, ∃ M : Submodule (ZMod d) (DiscretePhaseSpace d n),
      (∀ x ∈ M, ∀ y ∈ M, symplecticBracket x y = 0) ∧
      {x | ((d : ℝ) ^ n)⁻¹ * Real.sqrt (1 - 1 / (2 * (d : ℝ) ^ 2)) < discreteWigner v x} ⊆
        {x | x - a ∈ M} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
