-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_pureCQ_extreme_cpt_iff
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.pureCQ_extreme_cpt_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:29.060234+00:00
-- url     : https://prove2.me/theorems/6720aed2-44c0-43bd-8943-615e26454db2
-- title:
--   Theorem 5(B): CPT extremality of an extreme CQ map
-- statement:
--   Let $d\ge1$, let $e_k$ be an orthonormal basis of $\mathbb C^d$, and let $\psi_k$ be arbitrary unit vectors. For the supplied representation $\Phi(X)=\sum_k|\psi_k\rangle\langle\psi_k|\langle e_k|X|e_k\rangle$,
--
--   $$\Phi\in\operatorname{ext}(\mathrm{CPT}_d)\quad\Longleftrightarrow\quad\langle\psi_j|\psi_k\rangle\ne0\quad\text{for all }j,k.$$
--
--   No orthogonality or independence assumption on outputs is imposed. This characterizes which pure-output CQ maps remain extreme in the larger channel set.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 5(B): CPT extremality of an extreme CQ map, PDF p. 7. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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

























































/-- Theorem 5(B), PDF pp.7–8: overlaps in the supplied Eq.(8) representation. -/
theorem pureCQ_extreme_cpt_iff (d : ℕ) (hd : 0 < d)
    (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (psi : Fin d → StateVector d)
    (hpsi : ∀ k, IsState (psi k)) :
    pureCQEndomorphism e psi ∈ (cptSet d).extremePoints ℝ ↔
      ∀ j k, inner ℂ (psi j) (psi k) ≠ 0 := by sorry












end QAlgorithms.Papers.Independent.Independent1.P02
