-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_coherent_projector_span
-- name    : QAlgorithms.Papers.Independent.Support21.P16.coherent_projector_span
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:40:43.480972+00:00
-- url     : https://prove2.me/theorems/f8b30afc-2fb6-4481-bb3d-a646631fa015
-- title:
--   Coherent projectors span all Bose operators
-- statement:
--   Let $d>0$ and $n\ge1$ be integers, and let $s_n$ be the Bose projector in $(\mathbb C^d)^{\otimes n}$. For every ambient complex operator $A$,
--   $$
--   A\in\operatorname{span}_{\mathbb C}
--   \bigl\{|\phi^{\otimes n}\rangle\langle\phi^{\otimes n}|:
--   \phi\in\mathbb C^d,\ \|\phi\|=1\bigr\}
--   \quad\Longleftrightarrow\quad A=s_nA=As_n.
--   $$
--   Thus normalized coherent projectors span the entire complex operator algebra on the Bose sector, including operators that are not density matrices. This is the operator-span assertion, distinct from the vector-span assertion on page 5.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 10, coherent-projector-span

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF pp.7,10: COMPLEX linear span of normalized coherent projectors is
the entire Bose operator corner, including nonpositive operators. -/
theorem coherent_projector_span (d n : ℕ) (hd : 0 < d) (hn : 1 ≤ n) :
    ∀ A : TensorMat d n,
      (A ∈ Submodule.span ℂ {B : TensorMat d n |
        ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧
          B = QAlgorithms.pureDensity (coherentTensor n phi)}) ↔ BoseSupported A := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
