-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_explicit_energy_gradient
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.explicit_energy_gradient
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:14:18.427165+00:00
-- url     : https://prove2.me/theorems/0653a04e-efa6-437b-af82-63159552b66e
-- title:
--   Static updates: explicitly computable energy gradient for global optimization
-- statement:
--   Let $N,D\ge1$ and fix admissible RAGE data giving a nonzero raw vector $v$ and a Hermitian Hamiltonian $H$. Along any differentiable real parameter path through these data, let $\dot v$ be the explicit finite-product derivative: replace one site tensor or one local rotation at a time by its derivative and differentiate each graph phase as $\frac{d}{dt}e^{i\theta}=i\dot\theta e^{i\theta}$. Write $f=\langle v,Hv\rangle$ and $g=\|v\|^2>0$. Then
--
--   $$\frac{dE}{dt}=\frac{g\,2\operatorname{Re}\langle\dot v,Hv\rangle-f\,2\operatorname{Re}\langle\dot v,v\rangle}{g^2}.$$
--
--   The Lean statement specifies the finite sums for $\dot v$ and assumes differentiability only of the supplied scalar parameter entries. In particular the formula applies to real coordinates of the tensors and graph and to valid smooth charts of the unitary rotations. It supplies an explicit gradient without an optimization convergence claim.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 3, Static updates: explicitly computable energy gradient for global optimization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.3, final Static updates sentence: the gradient is explicitly computable.
For every differentiable real coordinate path, the raw derivative is the displayed finite
sum, and the energy derivative is the quotient rule with a positive norm denominator.
There is no optimizer convergence or global-optimality conclusion. -/
theorem explicit_energy_gradient {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (hv : rage A G V ≠ 0) (H : Matrix (Qubits N) (Qubits N) ℂ) (hH : H.IsHermitian)
    (t0 : ℝ) (Ap : ℝ → Tensors N D) (wp : ℝ → Fin N → Fin N → ℝ)
    (Vp : ℝ → Fin N → Matrix Bool Bool ℂ)
    (Adot : Tensors N D) (wdot : Fin N → Fin N → ℝ)
    (Vdot : Fin N → Matrix Bool Bool ℂ)
    (hA0 : Ap t0 = A) (hw0 : wp t0 = G.weight)
    (hV0 : Vp t0 = fun k => (V k : Matrix Bool Bool ℂ))
    (hAp : ∀ k b i j, HasDerivAt (fun t => Ap t k b i j) (Adot k b i j) t0)
    (hwp : ∀ i j, HasDerivAt (fun t => wp t i j) (wdot i j) t0)
    (hVp : ∀ k a b, HasDerivAt (fun t => Vp t k a b) (Vdot k a b) t0) :
    let v := rage A G V
    let vdot := rawTangent A Adot G.weight wdot (fun k => (V k : Matrix Bool Bool ℂ)) Vdot
    let path := fun t => act (productOp (Vp t)) (act (graphOp (wp t)) (traceMPS (Ap t)))
    let f := (inner ℂ v (act H v)).re
    let g := ‖v‖ ^ 2
    HasDerivAt path vdot t0 ∧
    HasDerivAt (fun t => rayleighEnergy H (path t))
      ((g * (2 * (inner ℂ vdot (act H v)).re) -
        f * (2 * (inner ℂ vdot v).re)) / g ^ 2) t0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
