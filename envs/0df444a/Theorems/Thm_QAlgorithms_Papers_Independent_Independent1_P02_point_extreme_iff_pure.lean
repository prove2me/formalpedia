-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_point_extreme_iff_pure
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.point_extreme_iff_pure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:52.107853+00:00
-- url     : https://prove2.me/theorems/05dc5d86-bb33-49c8-9640-619dd4c2631f
-- title:
--   Introduction: extremality of a point channel
-- statement:
--   Let $d\ge1$ and let $R$ be a density matrix on $\mathbb C^d$. Define the replacement map $\Phi_R(X)=\operatorname{Tr}(X)R$ on all operators. Then
--
--   $$\Phi_R\text{ is extreme in CPT}\ \Longleftrightarrow\ R\text{ is pure}\ \Longleftrightarrow\ \Phi_R\text{ is extreme in EBT}.$$
--
--   Here pure means $R=|\psi\rangle\langle\psi|$ for a unit vector $\psi$. Both ambient convex sets are recorded, as supported by the point-channel paragraph and Theorem 5(A),(B).
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Introduction: extremality of a point channel, PDF p. 3. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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





















































/-- Introduction, PDF p.3: point-channel extremality. Both CPT and EBT readings
are supported by Theorem 5(A),(B) with identical output vectors. -/
theorem point_extreme_iff_pure (d : ℕ) (hd : 0 < d) (R : Algebra d)
    (hR : IsDensityMatrix R) :
    (pointEndomorphism R ∈ (cptSet d).extremePoints ℝ ↔ IsPureDensity R) ∧
    (pointEndomorphism R ∈ (ebtSet d).extremePoints ℝ ↔ IsPureDensity R) := by sorry
















end QAlgorithms.Papers.Independent.Independent1.P02
