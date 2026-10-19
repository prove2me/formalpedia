-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_ebt_cptExtreme_is_pureCQ
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.ebt_cptExtreme_is_pureCQ
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:17:36.433057+00:00
-- url     : https://prove2.me/theorems/5d61e116-6258-4244-a6f2-2405817f32ef
-- title:
--   Theorem 5(C): EBT and CPT-extreme implies extreme CQ
-- statement:
--   Let $d\ge1$. If $\Phi$ is EBT and is an extreme point of the set of CPT maps, then
--
--   $$\Phi\text{ is a pure-output CQ map}.$$
--
--   Explicitly, an orthonormal input basis and unit output vectors realizing Eq.(8) exist. Neither Choi rank $d$ nor a $d$-term Kraus representation is assumed: those are proof conclusions. This identifies the overlap of EBT with the extreme points of CPT.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 5(C): EBT and CPT-extreme implies extreme CQ, PDF p. 7. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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


























































/-- Theorem 5(C), PDF p.7, proof p.11 using Lemma 8. -/
theorem ebt_cptExtreme_is_pureCQ (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d)
    (hEBT : Phi ∈ ebtSet d) (hExtreme : Phi ∈ (cptSet d).extremePoints ℝ) :
    IsPureCQ Phi := by sorry











end QAlgorithms.Papers.Independent.Independent1.P02
