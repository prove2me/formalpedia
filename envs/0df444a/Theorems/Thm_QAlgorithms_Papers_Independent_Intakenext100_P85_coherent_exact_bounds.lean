-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_coherent_exact_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.coherent_exact_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:19:06.667576+00:00
-- url     : https://prove2.me/theorems/abcfc92e-c00b-4ec3-9644-43f5a8881acc
-- title:
--   Eqs.(11),(13): exact coherent Chernoff/Bhattacharyya bounds
-- statement:
--   Let $N_S,N_B\ge0$, $0<\kappa<1$, and $M\ge1$. Transmit $M$ coherent modes each of real amplitude $\sqrt{N_S}$ through independent copies of the target channel. The hypotheses have priors $1/2$, and reception permits every joint quantum measurement. The one-mode returned states $\rho_0,\rho_1$ are Gaussian, with means $(0,0)$ and $(\sqrt{\kappa N_S},0)$ and common covariance $(2N_B+1)I/4$. Set
--   $$
--   c=\kappa N_S(\sqrt{N_B+1}-\sqrt{N_B})^2.
--   $$
--   Their actual operator overlap satisfies $\operatorname{Tr}(\rho_0^{1/2}\rho_1^{1/2})=e^{-c}$, and the optimized quantum Chernoff bound equals the Bhattacharyya bound $e^{-Mc}/2$. The minimum equal-prior error obeys
--   $$
--   \frac{1-\sqrt{1-e^{-2Mc}}}{2}\le P_{e,\mathrm{CS}}^{(M)}\le\frac{e^{-Mc}}2.
--   $$
--   All states are constructed from the coherent input and physical channel; Gaussian moments and bounded realizations are conclusions. These finite-parameter bounds remain valid at zero signal energy or zero background.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 3, Eqs.(11),(13): exact coherent Chernoff/Bhattacharyya bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.3, Eqs.(11),(13): exact coherent-state overlap, Chernoff
minimum and finite-copy equal-prior error sandwich. All joint effects are
allowed. Real source means are (sqrt(k NS),0), not (sqrt(k)*NS,0). -/
theorem coherent_exact_bounds (k NS NB : ℝ) (hk : 0 < k) (hk1 : k < 1)
    (hNS : 0 ≤ NS) (hNB : 0 ≤ NB) (M : ℕ) (hM : 0 < M)
    (W : G.FockWeylSystem 1) :
    let alpha := constantAmplitude 1 NS
    let rho0 := coherentReturn false k NB alpha
    let rho1 := coherentReturn true k NB alpha
    (∀ present : Bool,
      BlockRealized M present k NB (coherentArray (constantAmplitude M NS)) ∧
      T.IsDensity (coherentReturn present k NB (constantAmplitude M NS)) ∧
      HasArray (realizeOccupationArray (coherentReturn present k NB (constantAmplitude M NS)))
        (coherentReturn present k NB (constantAmplitude M NS))) ∧
    SourceGaussian W rho0 0 (Matrix.diagonal (fun _ => bathB NB / 4)) ∧
    SourceGaussian W rho1
      (fun i => if i.2 = 0 then Real.sqrt (k * NS) else 0)
      (Matrix.diagonal (fun _ => bathB NB / 4)) ∧
    G.chernoffTrace (realizeOccupationArray rho0) (realizeOccupationArray rho1) (1 / 2) =
      Real.exp (-coherentExponent k NS NB) ∧
    G.quantumChernoff (realizeOccupationArray rho0) (realizeOccupationArray rho1) M =
      ENNReal.ofReal (Real.exp (-(M : ℝ) * coherentExponent k NS NB) / 2) ∧
    ENNReal.ofReal (coherentLower k ((M : ℝ) * NS) NB) ≤
      optimumError (coherentReturn false k NB (constantAmplitude M NS))
        (coherentReturn true k NB (constantAmplitude M NS)) ∧
    optimumError (coherentReturn false k NB (constantAmplitude M NS))
        (coherentReturn true k NB (constantAmplitude M NS)) ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) * coherentExponent k NS NB) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
