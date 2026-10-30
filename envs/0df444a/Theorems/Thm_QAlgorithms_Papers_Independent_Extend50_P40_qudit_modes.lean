-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_qudit_modes
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.qudit_modes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:23:53.271215+00:00
-- url     : https://prove2.me/theorems/1d3780e5-4aa4-4332-a385-f0e281cbb2f7
-- title:
--   §VI.A.3 Eq.(105): 1→2 cloning of a mode-encoded qudit
-- statement:
--   Let $d\ge2$. In the selected one-emission sector of a coherent equal-coupling d-mode amplifier, the fixed isometry sends an arbitrary normalized input $\psi$ to $[2(d+1)]^{-1/2}\sum_j(\psi\otimes|j\rangle+|j\rangle\otimes\psi)\otimes|j\rangle$. Both actual marginals have
--
--   $$
--   \rho_j=\frac{d+2}{2(d+1)}|\psi\rangle\langle\psi|+\frac{I}{2(d+1)},\qquad F_j=\frac{d+3}{2(d+1)}.
--   $$
--
--   This includes all coherent superpositions of input modes. One input photon, exactly two selected output photons, and coherence between mode amplitudes are built into the emission map.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 28, §VI.A.3 Eq.(105): 1→2 cloning of a mode-encoded qudit

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- VI.A.3, PDF p.28 Eq.(105): one photon in an arbitrary coherent mode
superposition, one equal-coupling emission, and two photons selected at output.
The same fidelity holds on EVERY normalized superposition, not only basis states. -/
theorem qudit_modes (d : ℕ) (hd : 2 ≤ d) :
    (modeEmission d)ᴴ * modeEmission d = 1 ∧ IsChannel (cloneChannel (modeEmission d)) ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 → ‖modeOutput psi‖ = 1 ∧
      cloneMarginalA (modeOutput psi) = depol (((d : ℝ) + 2) / (2 * (d + 1))) (pureDensity psi) ∧
      cloneMarginalB (modeOutput psi) = depol (((d : ℝ) + 2) / (2 * (d + 1))) (pureDensity psi) ∧
      pureFidelity psi (cloneMarginalA (modeOutput psi)) = ((d : ℝ) + 3) / (2 * (d + 1)) ∧
      pureFidelity psi (cloneMarginalB (modeOutput psi)) = ((d : ℝ) + 3) / (2 * (d + 1))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
