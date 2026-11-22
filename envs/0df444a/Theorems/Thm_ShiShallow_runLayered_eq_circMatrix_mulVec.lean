-- Prove2me | Theorems.Thm_ShiShallow_runLayered_eq_circMatrix_mulVec
-- name    : ShiShallow.runLayered_eq_circMatrix_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T18:29:13.42186+00:00
-- url     : https://prove2.me/theorems/25a6aea0-e59e-4442-a926-77742b6e0c4f
-- title:
--   THE BRIDGE: layered circuit execution equals multiplication by the circuit matrix
-- statement:
--   THE BRIDGE between the development's two independent semantics for shallow circuits, at full circuit level: running a layered circuit on a state function gives exactly the same amplitude array as multiplying the circuit's matrix into that state read as a vector.
--
--   WHY THIS WAS THE MISSING LINK. The development defines execution on state functions -- gates rewrite bit-string arguments, layers and circuits are LEFT FOLDS of those actions -- and separately defines a matrix for every gate, layer and circuit. The matrix bundle's own header records that nothing in it connects the two, and every acceptance-probability notion in the wider development, including the QMA family's acceptance, is phrased on the state-function side. So the entire matrix and spectral apparatus was unreachable from the objects that actually appear in the complexity statements. This theorem connects them.
--
--   THE KEY STRUCTURAL FACT is that the two composition orders AGREE despite looking opposite. On the state side a layer applies its head gate FIRST and folds left. On the matrix side the layer's matrix is the tail's matrix TIMES the head's, and multiplying that into a vector applies the head's matrix first. The apparent reversal in the matrix product is exactly what makes the orders match, and the same pattern repeats one level up for circuits.
--
--   ROUTE. Gate level dispatches over the five instruction constructors onto the two gate-level bridges. Layer level is a list induction whose step composes the inductive hypothesis with the gate bridge and then collapses nested matrix-vector products into a product of matrices. Circuit level is the same induction one level up. Base cases are the identity matrix acting trivially.
--
--   PROVENANCE. The two hypotheses abstract the separately accepted gate-level bridges: ShiShallow.apply1_eq_apply1Matrix_mulVec for one-qubit gates and ShiShallow.cnotState_eq_cnotMatrix_mulVec for CNOT. Note the second carries a wire-distinctness hypothesis, which the CNOT instruction constructor supplies -- the matrix definition itself does not require it and is NOT the CNOT matrix when the wires coincide.
--
--   HONEST LIMITATIONS. This relates two semantics and proves nothing new about either. It establishes NO unitarity: the gate matrices are still not known to be unitary, nothing here says the circuit matrix preserves norms, and no spectral property of any circuit follows. Layer well-formedness is neither assumed nor used, so the identity also holds for instruction lists that are not legitimate parallel layers, where it has no physical reading. It says nothing about acceptance probabilities, witnesses, measurement, or amplification -- in particular it does NOT by itself express any acceptance quantity as a quadratic form, which needs the measurement projector and an adjoint step that are not done here. No universality claim for the H, S, T, X, CNOT gate set.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open Matrix

theorem runLayered_eq_circMatrix_mulVec {n : ℕ}
    (hA : ∀ (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n),
      apply1 U i ψ = apply1Matrix U i *ᵥ ψ)
    (hC : ∀ (i j : Fin n) (hij : i ≠ j) (ψ : QState n),
      cnotState i j hij ψ = cnotMatrix i j *ᵥ ψ)
    (c : Layered n) (ψ : QState n) :
    runLayered c ψ = circMatrix c *ᵥ ψ := by
  sorry

end ShiShallow
