-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_activation_multiplicities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.activation_multiplicities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:44:17.326721+00:00
-- url     : https://prove2.me/theorems/668300e3-65bc-4449-9b5c-9b32835619ae
-- title:
--   Multiplicities of first- and second-order activation spaces
-- statement:
--   Use the real Specht models indexed by partitions in the paper’s order. For $n\ge2$, the first-order permutation representation has multiplicities $1,1$ on $(n),(n-1,1)$. For $n\ge4$, use the four shapes $(n),(n-1,1),(n-2,2),(n-2,1,1)$. The ordered off-diagonal and full matrix representations have types
--
--   $$
--   \tau_{\rm off}=(1,2,1,1),\qquad \tau_{\rm full}=(2,3,1,1).
--   $$
--
--   All other multiplicities are zero. Here a type means the existence of an actual invertible equivariant real linear identification with the corresponding copies of the concrete Specht modules, not just equality of dimensions. These decompositions explain the parameter counts of the second-order layers.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 4, §4 and §10.1, unnumbered: activation multiplicities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Unnumbered activation multiplicities, source PDF p.4 and p.15.
First-order range n≥2; the four-shape stable range is n≥4. Trailing copies are zero. -/
theorem activation_multiplicities :
    (∀ (n : ℕ), 2 ≤ n →
      ∀ lambda : Fin 2 → QAlgorithms.Schur.Partition n n,
        (∀ a, (lambda a).val.rowLens = (![[n], [n-1,1]] : Fin 2 → List ℕ) a) →
        HasTensorType (⊤ : Submodule ℝ (Tensor n 1)) lambda ![1,1]) ∧
    (∀ (n : ℕ), 4 ≤ n →
      ∀ lambda : Fin 4 → QAlgorithms.Schur.Partition n n,
        (∀ a, (lambda a).val.rowLens = secondShapes n a) →
        HasTensorType (DistinctSpace n 2) lambda ![1,2,1,1] ∧
        HasTensorType (⊤ : Submodule ℝ (Tensor n 2)) lambda ![2,3,1,1]) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
