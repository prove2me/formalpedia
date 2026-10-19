-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_holevo_coordinate_factorization
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.holevo_coordinate_factorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:19:08.622627+00:00
-- url     : https://prove2.me/theorems/b425b744-7956-4904-942c-79bc2f1fc585
-- title:
--   Section 4: Holevo coordinate factorization and trace-preserving row
-- statement:
--   In the preceding Hermitian basis, let $R_k$ be density matrices and $F_k$ positive semidefinite effects, $k=1,\ldots,m$. Define $W_{jk}=\operatorname{Tr}(R_kG_j)$, $U_{nk}=\operatorname{Tr}(F_kG_n)$ and $T_{jn}=\operatorname{Tr}(G_j\Phi(G_n))$ for the computed Holevo map. Then
--
--   $$T_{jn}=\sum_kW_{jk}U_{nk},\qquad T=WU^{\mathsf T}.$$
--
--   Moreover, $F$ is a POVM if and only if the first row of $T$ is $(1,0,\ldots,0)$. Both factors have $d^2$ rows and $m$ columns. The product corrects the printed $W^{\mathsf T}U$ according to those dimensions and the unchanged entrywise formula. Independent moderation of this correction is required.
--
--   **Correction to the printed source.**
--
--   Printed: The source prints T=W^T U although W and U are d^2 by N.
--
--   Corrected: Use T=W U^T and retain the source's unchanged entrywise sum t_jn=sum_k w_jk u_nk.
--
--   Reason: W^T U has shape N by N, while W U^T has the required d^2 by d^2 shape and exactly the printed entries.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Section 4: Holevo coordinate factorization and trace-preserving row, PDF p. 12. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02



































































/-- Section 4, PDF pp.12–13. Proposed correction T=W U^T replaces the
dimensionally invalid W^T U; the entrywise formula is unchanged.
Pending independent source moderation. -/
theorem holevo_coordinate_factorization (d m : ℕ) (G : HermitianFrame d)
    (R F : Fin m → Algebra d) (hR : ∀ k, IsDensityMatrix (R k))
    (hF : ∀ k, (F k).PosSemidef) :
    coordinateMatrix G (Entanglement.holevoMap R F) =
      (coordinateFactors G R F).1 * (coordinateFactors G R F).2.transpose ∧
    (∀ j n, coordinateMatrix G (Entanglement.holevoMap R F) j n =
      ∑ k, hermitianCoordinates G (R k) j * hermitianCoordinates G (F k) n) ∧
    (IsPOVM F ↔ ∀ n, coordinateMatrix G (Entanglement.holevoMap R F)
      ⟨0,by have := G.positive; positivity⟩ n = if n.val = 0 then 1 else 0) := by sorry


end QAlgorithms.Papers.Independent.Independent1.P02
