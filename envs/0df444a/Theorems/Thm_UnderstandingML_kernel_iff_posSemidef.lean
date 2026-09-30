-- Prove2me | Theorems.Thm_UnderstandingML_kernel_iff_posSemidef
-- name    : UnderstandingML.kernel_iff_posSemidef
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:48:52.824654+00:00
-- url     : https://prove2.me/theorems/6e0b9d56-b2f8-4bb2-922c-35d554ea7fe0
-- title:
--   Lemma 16.2: a symmetric K implements an inner product in some Hilbert space iff all its Gram matrices are positive semidefinite
-- statement:
--   **Lemma 16.2.** A symmetric function $K : X \times X \to \mathbb{R}$ implements an inner product in some Hilbert space if and only if it is positive semidefinite; namely, for all $x_1, \dots, x_m$, the Gram matrix $G_{ij} = K(x_i, x_j)$ is a positive semidefinite matrix.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.2.2 p. 222, Lemma 16.2 with its proof

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

namespace UnderstandingML

/-- **Lemma 16.2** (p. 222). A symmetric function `K : X × X → ℝ` implements an inner product in
some Hilbert space if and only if it is positive semidefinite: for all `x₁, …, x_m`, the Gram
matrix `Gᵢⱼ = K(xᵢ, xⱼ)` is positive semidefinite. -/
theorem kernel_iff_posSemidef {X : Type u} (K : X → X → ℝ) (hsymm : ∀ x x', K x x' = K x' x) :
    IsKernel K ↔ ∀ (m : ℕ) (x : Fin m → X), (gramMatrix K x).PosSemidef := by sorry

end UnderstandingML
