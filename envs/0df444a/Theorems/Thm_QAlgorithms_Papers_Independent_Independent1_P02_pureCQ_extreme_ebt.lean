-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_pureCQ_extreme_ebt
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.pureCQ_extreme_ebt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:05.953978+00:00
-- url     : https://prove2.me/theorems/51334ed7-5fd1-4970-b0f1-0a8168ac0a39
-- title:
--   Theorem 5(A): extreme CQ implies extreme EBT
-- statement:
--   Let $d\ge1$ and let $\Phi$ be an extreme CQ map in the source's terminology: for an orthonormal basis $e_k$ and unit vectors $\psi_k$,
--
--   $$\Phi(X)=\sum_k|\psi_k\rangle\langle\psi_k|\langle e_k|X|e_k\rangle.$$
--
--   Then $\Phi$ is an extreme point of the convex set of EBT maps. The vectors $\psi_k$ may coincide or be dependent. The source-defined class is therefore distinguished from convex extremality itself.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 5(A): extreme CQ implies extreme EBT, PDF p. 7. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02
























































/-- Theorem 5(A), PDF p.7, proof pp.7–8. -/
theorem pureCQ_extreme_ebt (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d)
    (hPhi : IsPureCQ Phi) : Phi ∈ (ebtSet d).extremePoints ℝ := by sorry













end QAlgorithms.Papers.Independent.Independent1.P02
