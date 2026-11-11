-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_projection_bad
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.projection_bad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:17:07.997467+00:00
-- url     : https://prove2.me/theorems/3594b834-f0ad-47f5-b2cd-368bfde7bf41
-- title:
--   BDL26 Two Sector Bad Projector: projection bad
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the projection bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L70-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L70-L71

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.projection_bad (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    IsStarProjection (1 - Pjoint S n BX BZ) := by sorry
