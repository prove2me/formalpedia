-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pX_bounds
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.pX_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:03:58.91325+00:00
-- url     : https://prove2.me/theorems/cbc6378b-6197-4327-a485-0ae597e25d3e
-- title:
--   BDL26 Two Sector Bad Projector: p X bounds
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the p X bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L121-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L121-L123

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.pX_bounds (β : ℝ) (BX : Finset (XImage S n)) :
    0 ≤ pX S n β BX ∧ pX S n β BX ≤ 1 := by sorry
