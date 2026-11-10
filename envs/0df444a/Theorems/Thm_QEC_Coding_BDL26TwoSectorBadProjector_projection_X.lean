-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_projection_X
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.projection_X
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:55:28.741422+00:00
-- url     : https://prove2.me/theorems/30d19112-9df8-4df9-9559-77a45800f2f9
-- title:
--   BDL26 Two Sector Bad Projector: projection X
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the projection X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L63-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L63-L64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25

theorem QEC.Coding.BDL26TwoSectorBadProjector.projection_X (BX : Finset (XImage S n)) : IsStarProjection (PX S n BX) := by sorry
