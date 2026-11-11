-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_psd_blocks
-- name    : PauliUnclonable531.Pauli.psd_blocks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:08.362943+00:00
-- url     : https://prove2.me/theorems/53a9eb50-04ec-4b95-8b93-d301d16f945b
-- title:
--   Lemma 2.8 — both PSD block-matrix equivalences
-- statement:
--   Let A,B,C be arbitrary complex square Hermitian operators of the same finite dimension. Both statements hold:
--
--   $$C\succ0\ \Longrightarrow\ \left(\begin{pmatrix}A&B\\B&C\end{pmatrix}\succeq0\iff A-BC^{-1}B\succeq0\right),$$
--   $$\begin{pmatrix}A&B\\B&A\end{pmatrix}\succeq0\iff(A-B\succeq0\ \text{and}\ A+B\succeq0).$$
--
--   The first clause requires only C to be positive definite; A may be singular. The second has no definiteness premise. This retains both implications in each equivalence and both conclusions on the second right-hand side.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Lemma 2.8, pp.13–14

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Operators

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Both clauses and both directions of Lemma 2.8, pp.13–14. The second clause
requires neither positive definiteness nor invertibility of A, B, or C. -/
theorem psd_blocks {A : Type} [Fintype A] [DecidableEq A]
    (X Y Z : Op A) (hX : X.IsHermitian) (hY : Y.IsHermitian) (hZ : Z.IsHermitian) :
    (Z.PosDef → ((Matrix.fromBlocks X Y Y Z).PosSemidef ↔ (X - Y * Z⁻¹ * Y).PosSemidef)) ∧
    ((Matrix.fromBlocks X Y Y X).PosSemidef ↔ (X - Y).PosSemidef ∧ (X + Y).PosSemidef) := by sorry

end PauliUnclonable531.Pauli
