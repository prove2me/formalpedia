-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_black_box_no_cloning
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.black_box_no_cloning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:16:27.62211+00:00
-- url     : https://prove2.me/theorems/e2b7db4b-377e-476a-a971-7ee9e5623556
-- title:
--   General finite quantum black-box no-cloning with attained minimax error
-- statement:
--   Let $\Phi_0,\Phi_1$ be two known finite-dimensional CPTP devices of the same nonempty input and output type. This model includes preparations through a one-dimensional input, general channels, and measuring devices through classical-output channels. A physical one-call discrimination procedure prepares a normalized probe with a reference register, invokes the unknown device on the probe once, and measures a binary POVM. Let $e_0(T)$ and $e_1(T)$ be its two conditional error probabilities and set
--
--   $$p=\inf_T\max\{e_0(T),e_1(T)\}.$$
--
--   This infimum is attained by a physical test and $0\le p\le1/2$. If one deterministic circuit, chosen independently of the unknown label, uses the device once and implements $\Phi_i\otimes\Phi_i$ on every bipartite input for both $i=0,1$, then
--
--   $$p=0\quad\text{or}\quad p=\tfrac12.$$
--
--   Conversely, perfect one-call discrimination permits exact cloning by preparing the identified known device twice. The result covers device cloning rather than only cloning unknown unitaries.
--
--   **Formalization Note** Physical tests use input-dimensional reference registers, normalized density matrices and normalized finite POVMs; arbitrary finite references compress to this size. The minimizing test is a conclusion, not an assumed optimizer. The cloning network has arbitrary finite memory and CPTP preprocessing and postprocessing.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 1, Unnumbered no-cloning theorem; footnotes [17]–[18], p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.1 and footnotes [17]–[18], p.4: general finite quantum-device no-cloning.
States and measuring devices enter as preparation and classical-output channels,
not as unknown unitaries. The minimax value is attained without assuming equal
conditional errors. Perfect discrimination conversely permits cloning by
conditional preparation of the known device. -/
theorem black_box_no_cloning {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (Phi0 Phi1 : Superop I O) (h0 : IsChannel Phi0) (h1 : IsChannel Phi1) :
    (∃ test : DeviceTest I O Bool,
      worstError Phi0 Phi1 test = minimaxError Phi0 Phi1 ∧
      ∀ other : DeviceTest I O Bool,
        worstError Phi0 Phi1 test ≤ worstError Phi0 Phi1 other) ∧
    (0 ≤ minimaxError Phi0 Phi1 ∧ minimaxError Phi0 Phi1 ≤ 1 / 2) ∧
    (ExactlyClonable (binaryDevices Phi0 Phi1) →
      minimaxError Phi0 Phi1 = 0 ∨ minimaxError Phi0 Phi1 = 1 / 2) ∧
    (PerfectlyDiscriminable (binaryDevices Phi0 Phi1) →
      ExactlyClonable (binaryDevices Phi0 Phi1)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
