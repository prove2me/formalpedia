-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_invariant_symmetric_purification
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.invariant_symmetric_purification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:59:41.336219+00:00
-- url     : https://prove2.me/theorems/12bc226b-e661-4873-b363-76071f22b753
-- title:
--   Lemma 3: cited symmetric purification of invariant states
-- statement:
--   Every normalized density operator $\rho$ on $\mathcal H^{\otimes n}$ invariant under permutations of its $n$ sites has a unit purification $\psi\in(\mathcal H\otimes\mathcal H)^{\otimes n}$ invariant under simultaneous permutations of the paired sites. Tracing the second factor of each pair from $|\psi\rangle\langle\psi|$ returns $\rho$. The reference has the same single-site dimension as $\mathcal H$. This includes $n=0$ and is the cited Renner lemma.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 15, Appendix Lemma 3: cited symmetric purification of invariant mixed states

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.15, Lemma 3, cited Lemma 4.2.2 of Renner (17).
An invariant MIXED state has a unit purification symmetric in the PAIRED sites;
the reference has the same single-site dimension. Zero sites are allowed. -/
theorem invariant_symmetric_purification {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (n : ℕ) (rho : Op (Copies I n)) (hrho : IsDensityMatrix rho)
    (hinv : InvariantCopyState rho) :
    ∃ psi : Vec (Copies (I × I) n), IsState psi ∧
      (∀ (pi : Equiv.Perm (Fin n)) (x : Copies (I × I) n), psi (x ∘ pi) = psi x) ∧
      discardReferences (pureDensity psi) = rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
