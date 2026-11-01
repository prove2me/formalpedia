-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_classical_perfect_measurement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.classical_perfect_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:21:27.923+00:00
-- url     : https://prove2.me/theorems/54db1f60-6dc5-4f66-b9aa-9dcfa34c2408
-- title:
--   Eq.(19) and pp.3–4: exact energy-constrained classical transmitter lower bound
-- statement:
--   Let $M\ge1$, $N_S,N_B\ge0$ and $0<\kappa<1$. Let $P(\alpha_S,\alpha_I)$ be a nonnegative measurable probability density relative to Lebesgue measure on $\mathbb C^M\times\mathbb C^M$, with finite ensemble signal energy
--   $$
--   \int P(\alpha_S,\alpha_I)\sum_{m=1}^M|\alpha_{S,m}|^2\,d^{2M}\alpha_S\,d^{2M}\alpha_I=MN_S.
--   $$
--   Prepare its mixture of signal/idler coherent projectors, transmit every signal mode through the target channel, and retain every idler mode. There is no IID or idler-energy restriction. Let $P_{e,\mathrm{class}}$ be the minimum equal-prior error over all joint return/idler effects, and let $P_{e,\mathrm{genie}}$ be the ensemble mean of the optimal coherent-return error when the full signal amplitude is revealed. Then
--   $$
--   \frac{1-\sqrt{1-\exp[-2M\kappa N_S(\sqrt{N_B+1}-\sqrt{N_B})^2]}}{2}
--   \le P_{e,\mathrm{genie}}\le P_{e,\mathrm{class}}.
--   $$
--   The input mixture, channel outputs and all coefficient integrals are genuine normalized trace-class densities, with integrability and bounded realizations included as conclusions. This is the exact perfect-measurement bound preceding the paper's asymptotic comparison.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 4, Eq.(19) and pp.3–4: exact energy-constrained classical transmitter lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source pp.3–4, Eq.(19) and the perfect-measurement argument using
(13): arbitrary correlated classical transmitter with average total signal
energy M NS. The P weight is a Lebesgue density as printed in (19).
No idler-energy constraint or IID assumption is imposed. -/
theorem classical_perfect_measurement (k NS NB : ℝ) (hk : 0 < k) (hk1 : k < 1)
    (hNS : 0 ≤ NS) (hNB : 0 ≤ NB) (M : ℕ) (hM : 0 < M)
    (P : ((Fin M → ℂ) × (Fin M → ℂ)) → ℝ) (hP : ClassicalDensity M NS P) :
    let X := classicalArray M P
    T.IsDensity X ∧ HasArray (realizeOccupationArray X) X ∧
    (∀ i j : Occ M × Occ M,
      Integrable (fun a => (P a : ℂ) * coherentArray a.1 i.1 j.1 *
        coherentArray a.2 i.2 j.2)) ∧
    (∀ present : Bool, TargetRealized M present k NB X ∧
      T.IsDensity (targetBlock M present k NB X) ∧
      HasArray (realizeOccupationArray (targetBlock M present k NB X)) (targetBlock M present k NB X)) ∧
    Integrable (genieIntegrand M k NB P) ∧
    ENNReal.ofReal (coherentLower k ((M : ℝ) * NS) NB) ≤
      ENNReal.ofReal (genieError M k NB P) ∧
    ENNReal.ofReal (genieError M k NB P) ≤
      optimumError (targetBlock M false k NB X) (targetBlock M true k NB X) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
