-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_local_process_tomography
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.local_process_tomography
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:00:13.207071+00:00
-- url     : https://prove2.me/theorems/72e4bba1-10f2-414e-a3af-89c958dacaf3
-- title:
--   Identifiability by local symmetric process tomography
-- statement:
--   Let n≥1 and let V,W be U(1)-invariant unitaries on n qubits. For a computational input x with x_r=1, write x^- for x with bit r changed to zero. For output strings y,z with w(y)=w(x)=w(z)+1 and every real θ, define the Bell-input symmetric measurement probability
--
--   $$p_V(x,r,y,z,\theta)=\frac14\left|V_{y,x}+e^{-i\theta}V_{z,x^-}\right|^2.$$
--
--   If all these probabilities agree for V and W, then W=e^{iα}V for some real α. The measurements are those of E4, implementable with symmetric two-local gates and computational measurements using the one Bell-pair ancilla. This is identifiability from probability data, without a finite-sample recovery claim.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 4, II.C / E: complete local symmetric process tomography

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.4,35, E1–E6: identifiability from all prescribed probabilities,
with a single Bell-pair ancilla. Printed E5 prose has the empty interval (pi,pi];
use all real settings of the periodic experiment, as E4/E6 require. This corrects
only that interval typo. This is not finite-sample exact recovery. -/
theorem local_process_tomography (n : ℕ) (hn : 1 ≤ n) (V W : QMat n)
    (hV : U1Unitary V) (hW : U1Unitary W)
    (hData : ∀ (x : Qubits n) (r : Fin n) (y z : Qubits n) (theta : ℝ),
      x r = true → qubitWeight y = qubitWeight x → qubitWeight z + 1 = qubitWeight x →
      bellInterference V x r y z theta = bellInterference W x r y z theta) :
    ∃ alpha : ℝ, W = Complex.exp (Complex.I*alpha) • V := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
