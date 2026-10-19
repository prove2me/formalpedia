-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_nondegenerate_phaseTest
-- name    : QAlgorithms.Papers.Independent.Information100.P07.nondegenerate_phaseTest
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:43:37.730833+00:00
-- url     : https://prove2.me/theorems/dda85be6-f877-4618-b98f-5cf561281085
-- title:
--   Unnumbered: residual local-phase test, Eq. (S43)
-- statement:
--   Let $\eta,\eta'$ be normalized two-qutrit blocks whose two marginal spectra match and are simple on the full qutrit spaces. Express both in product eigenbases with the same increasing eigenvalue order, so corresponding marginals are equal diagonal matrices. Then LU equivalence holds exactly when real local phases exist with
--   $$\eta'_{ij,kl}=e^{\mathrm i(\alpha_i-\alpha_k+\beta_j-\beta_l)}\eta_{ij,kl}.$$
--
--   The Lean statement uses the printed full-simple-spectrum regime, including any zero eigenvalue in the simplicity requirement. It makes no claim that phases suffice in a degenerate eigenspace.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 20, Unnumbered: residual local-phase test, Eq. (S43)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.20, Eq.(S43): full simple spectra in aligned ordered marginal eigenbases. -/
theorem nondegenerate_phaseTest (eta zeta : Joint)
    (he : IsDensityMatrix eta) (hz : IsDensityMatrix zeta)
    (hA : traceRight eta = Matrix.diagonal (fun i => (ascEigenvalues (traceRight eta) i : ℂ)))
    (hB : traceLeft eta = Matrix.diagonal (fun i => (ascEigenvalues (traceLeft eta) i : ℂ)))
    (hZA : traceRight zeta = traceRight eta) (hZB : traceLeft zeta = traceLeft eta)
    (hsimpleA : Function.Injective (ascEigenvalues (traceRight eta)))
    (hsimpleB : Function.Injective (ascEigenvalues (traceLeft eta))) :
    LU eta zeta ↔ PhaseRelated eta zeta := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
