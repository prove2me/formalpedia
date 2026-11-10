-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_badUnionWords_mem
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.badUnionWords_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:55:30.370192+00:00
-- url     : https://prove2.me/theorems/d0427b58-a570-4e24-beba-b213c97734ad
-- title:
--   BDL26 Two Sector Bad Projector: bad Union Words mem
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the bad Union Words mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L46-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L46-L61

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.badUnionWords_mem (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n))
    (u : XImage S n) (v : ZImage S n) :
    CSSGibbs.joinSyndrome u.val v.val ∈ badUnionWords S n BX BZ ↔ u ∈ BX ∨ v ∈ BZ := by sorry
