-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P36_idealPSKReading
-- name    : QAlgorithms.Papers.Independent.Advance50.P36.idealPSKReading
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:51:56.950012+00:00
-- url     : https://prove2.me/theorems/d440e69e-13fd-4214-a942-0b6a9096c8fd
-- title:
--   Ideal PSK reading: zero quasi-Bell error and the coherent benchmark
-- statement:
--   Let $\alpha\in\mathbb C\setminus\{0\}$ be a finite coherent amplitude, let $r=|\alpha|^2$, and let $p\in[0,1]$ and $1-p$ be the bit priors. The memory is ideal and lossless: bit zero does nothing, and bit one applies $U_B(\pi)=\exp(-i\pi N_B)$ to mode $B$, leaving reference mode $A$ unchanged. Write $\kappa=e^{-2r}$ and
--   $$
--   |\Psi_2\rangle=\frac{|\alpha,\alpha\rangle-|-\alpha,-\alpha\rangle}{\sqrt{2(1-\kappa^2)}},\qquad
--   |\Psi_4\rangle=\frac{|\alpha,-\alpha\rangle-|-\alpha,\alpha\rangle}{\sqrt{2(1-\kappa^2)}}.
--   $$
--   All coherent vectors are the canonical normalized vectors on full oscillator Fock spaces. These two quasi-Bell vectors are normalized, have finite mean photon number in each mode, and satisfy $(I_A\otimes U_B(\pi))|\Psi_2\rangle=|\Psi_4\rangle$. The coherent comparison vectors $|\alpha\rangle$ and $|-\alpha\rangle$ are normalized and have finite mean photon number as well.
--
--   For any normalized output pair $u,v$, let $\mathcal E_p(u,v)$ be the set of average errors $p(1-\langle u|T|u\rangle)+(1-p)\langle v|T|v\rangle$ over all bounded binary measurement effects $0\leq T\leq I$ on the entire output Hilbert space. Then both minima are attained and
--   $$
--   \min\mathcal E_p(\Psi_2,\Psi_4)=0,\qquad
--   \min\mathcal E_p(|\alpha\rangle,|-\alpha\rangle)
--   =\frac{1-\sqrt{1-4p(1-p)e^{-4r}}}{2}.
--   $$
--   The coherent minimum is strictly positive when $0<p<1$; it is zero at deterministic priors. This gives the paper's error-free finite-energy reading result together with its coherent benchmark. The schemes share the amplitude parameter; equality of their total energies is not asserted.
--
--   **Formalization Note** Coherent coefficient realization, unit norms, and summability of the actual photon weights are conclusions. `IsLeast` includes attainment and optimality against every binary POVM. The local phase multiplier corrects the missing imaginary unit in printed Eq. (8).
-- source:
--   Error free Quantum Reading by Quasi Bell State of Entangled Coherent States, arXiv:1108.4163v2, PDF p. 3, §IV, Eq.(18), with Eqs.(3)-(5),(14)-(16) and §V

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Eq.(18), with p.2 Eqs.(3)-(5) and p.3 §V: exact attained
minimum binary errors and finite-energy realization. The receiver ranges over
all binary effects on the full output Hilbert space. Both priors may be
endpoints; coherent error is strictly positive only for nontrivial priors.
No equality of single-mode and two-mode transmitter energies is asserted.
The phase action corrects the missing i in printed Eq.(8), PDF p.2. -/
theorem idealPSKReading (alpha : ℂ) (halpha : alpha ≠ 0)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuasiBellCoherentRealized alpha ∧
    CoherentWordRealized ![alpha] ∧ CoherentWordRealized ![-alpha] ∧
    ‖quasiBellState alpha 1‖ = 1 ∧ ‖quasiBellState alpha 3‖ = 1 ∧
    HasFinitePhotonEnergy (quasiBellState alpha 1) ∧
    HasFinitePhotonEnergy (quasiBellState alpha 3) ∧
    HasFinitePhotonEnergy (coherentWord ![alpha]) ∧
    HasFinitePhotonEnergy (coherentWord ![-alpha]) ∧
    modeBPhaseShift Real.pi (quasiBellState alpha 1) = quasiBellState alpha 3 ∧
    IsLeast (binaryErrorValues p (quasiBellState alpha 1)
      (modeBPhaseShift Real.pi (quasiBellState alpha 1))) 0 ∧
    IsLeast (binaryErrorValues p (coherentWord ![alpha]) (coherentWord ![-alpha]))
      (coherentReadingError alpha p) ∧
    (0 < p → p < 1 → 0 < coherentReadingError alpha p) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P36

end
