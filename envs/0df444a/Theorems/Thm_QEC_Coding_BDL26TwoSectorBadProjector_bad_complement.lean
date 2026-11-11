-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_bad_complement
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.bad_complement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:19:35.647652+00:00
-- url     : https://prove2.me/theorems/339e318e-4a65-4a19-be72-bc29bb72d097
-- title:
--   BDL26 Two Sector Bad Projector: bad complement
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the bad complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L93-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L93-L100

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.bad_complement (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    1 - Pjoint S n BX BZ =
      CSSGibbs.badProjector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
        (badUnionWords S n BX BZ) := by sorry
