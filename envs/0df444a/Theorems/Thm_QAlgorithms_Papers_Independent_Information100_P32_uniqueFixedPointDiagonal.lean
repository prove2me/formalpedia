-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_uniqueFixedPointDiagonal
-- name    : QAlgorithms.Papers.Independent.Information100.P32.uniqueFixedPointDiagonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:45:41.508984+00:00
-- url     : https://prove2.me/theorems/91d13599-6d65-4a8c-bf21-7bdb50244187
-- title:
--   A unique decoupled fixed point is diagonal; converse fails
-- statement:
--   Work in arbitrary finite nonempty system and ancillary Hilbert spaces with fixed orthonormal reference bases. Write $\mathcal D(X)_{ij}=\delta_{ij}X_{ii}$ for complete dephasing in the specified basis. A density matrix is positive semidefinite with trace one; a channel is completely positive and trace preserving. Population–coherence decoupling means that diagonal and zero-diagonal operator sectors are each invariant, on all operators. If $\Phi$ is decoupled and has a unique physical fixed point $\rho_*$, then
--   $$\mathcal D(\rho_*)=\rho_*.$$
--   Uniqueness ranges only over density matrices. Conversely, there exists a qubit CPTP channel with a unique diagonal physical fixed point whose diagonal and off-diagonal sectors are coupled. This conclusion does not infer convergence merely from uniqueness.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 18, Appendix A.4 Eqs.(A32)–(A33): unique decoupled fixed point is diagonal; converse fails

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.18, Eqs.(A32)–(A33): uniqueness is over physical density matrices.
The converse fails even for a channel with a unique diagonal physical fixed point. -/
theorem uniqueFixedPointDiagonal {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (f : Op I → Op I) (hf : IsChannel f) (hd : Decoupled f)
    (r : Op I) (hr : IsDensityMatrix r) (hfix : f r = r)
    (hunique : ∀ x, IsDensityMatrix x → f x = x → x = r) :
    diagonal r = r ∧
    (∃ (g : Op Bool → Op Bool) (s : Op Bool), IsChannel g ∧ IsDensityMatrix s ∧
      g s = s ∧ diagonal s = s ∧
      (∀ x, IsDensityMatrix x → g x = x → x = s) ∧ ¬Decoupled g) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
