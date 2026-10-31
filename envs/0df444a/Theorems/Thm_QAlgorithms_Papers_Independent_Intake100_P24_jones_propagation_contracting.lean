-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P24_jones_propagation_contracting
-- name    : QAlgorithms.Papers.Independent.Intake100.P24.jones_propagation_contracting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:15:55.314824+00:00
-- url     : https://prove2.me/theorems/9dcb39ae-d69c-4119-92d5-840232e1f622
-- title:
--   Standalone Jones propagation is contracting
-- statement:
--   Let $\Omega=\Omega^\dagger$ be the renormalized $2\times2$ frequency matrix and let $G,D\ge0$ be the absorption and decoherence matrices. For $t\ge0$, define the Jones propagator
--
--   $$V_t=\exp\!\left[-t\left(i\Omega+\tfrac12G+D\right)\right].$$
--
--   Then $V_tV_t^\dagger\le I$, and it acts on any unnormalized Jones vector by $\alpha\mapsto V_t\alpha$. This is the standalone contraction assertion (53) for the evolution (48).
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, PDF p. 9, §VI.B, (48),(49),(53): Jones contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- arXiv:1904.06170v1 PDF pp.8–9, (48),(49),(53): standalone Jones
propagation is contracting. omega is the Hermitian renormalized frequency.
No unit norm is imposed on the Jones amplitudes. -/
theorem jones_propagation_contracting
    (omega gamma gammaDec : PolarizationMatrix) (homega : omega.IsHermitian)
    (hgamma : gamma.PosSemidef) (hdec : gammaDec.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 - jonesPropagation omega gamma gammaDec t *
      (jonesPropagation omega gamma gammaDec t)ᴴ).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intake100.P24

end
