-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_even_tail_exact
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.even_tail_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:28:12.597872+00:00
-- url     : https://prove2.me/theorems/3a1a6cfe-6554-4257-8a5a-a35dd7b492e3
-- title:
--   BDL26 Two Sector Bad Projector: even tail exact
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the even tail exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L188-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L188-L192

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.even_tail_exact (k : Nat) (β : ℝ)
    (BX : Finset (XImage S (2*k))) (BZ : Finset (ZImage S (2*k))) :
    clbtGibbsTailMass (Pjoint S (2*k) BX BZ) (gibbs S (2*k) β) =
      pX S (2*k) β BX+pZ S (2*k) β BZ-pX S (2*k) β BX*pZ S (2*k) β BZ := by sorry
