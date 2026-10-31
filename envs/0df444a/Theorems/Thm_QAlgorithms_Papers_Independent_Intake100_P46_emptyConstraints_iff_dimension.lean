-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_emptyConstraints_iff_dimension
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.emptyConstraints_iff_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:05:06.600159+00:00
-- url     : https://prove2.me/theorems/d72fc4f0-2237-4dde-8bc5-d9d7507a58ad
-- title:
--   Empty restricted family leaves only the completion dimension
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   Use the balanced setting and the spectral, kernel-basis and compressed eigenbasis data of the preceding test. Let $V_W=\ker O_W$, and suppose the compressed operator has no nonzero eigenmodes, so its Hermitian constraint family is empty. Then every pair of vectors $v,w\in V_W$ obeys $(I-L_V)(|v\rangle\langle w|)=0$, and
--
--   $$W\text{ is purifiable}\quad\Longleftrightarrow\quad \dim V_W\ge\operatorname{rank}W.$$
--
--   The assertion that the bilinear constraints vanish does not assert that arbitrary vectors are mutually orthogonal or correctly normalized. The dimension condition is what permits a completion containing the prescribed $w_0$ with squared norm $d_{A_O}d_{B_O}$. The formal statement represents $V_W$ by its explicit orthonormal processCoordinates.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 7, §5, footnote 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF p.7, footnote 7: an empty nonzero-mode family removes the bilinear constraints;
normalization and orthogonality still require a completion, exactly when dim VW ≥ rank W.
PRINTED: no laboratory balance condition. CHANGED: require dAI*dBI=dAO*dBO.
WHY: the downstream reversible rank-sized reconstruction must be square, as in the
corrected Theorem 4; purifiability itself still allows independent past/future dimensions. -/
theorem emptyConstraints_iff_dimension {d : Fin 4 → ℕ+}
    (W : ProcessMatrix (laboratorySignature d 1 1)) (hW : IsValidProcess W)
    (e : SupportSpectrum W) (b : KernelBasisData e) (s : CompressionSpectrum b)
    (balanced : (d 0 : ℕ) * (d 2 : ℕ) = (d 1 : ℕ) * (d 3 : ℕ))
    (empty : ∀ k, s.values k = 0) :
    (∀ v w : Fin b.dimension → ℂ,
      invalidSubspaceProjector (vectorOuter (liftKernelVector b v) (liftKernelVector b w)) = 0) ∧
    (IsPurifiable W ↔ (e.rank : ℕ) ≤ b.dimension) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
