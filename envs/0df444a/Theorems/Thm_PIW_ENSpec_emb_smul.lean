-- Prove2me | Theorems.Thm_PIW_ENSpec_emb_smul
-- name    : PIW.ENSpec.emb_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:01.762992+00:00
-- url     : https://prove2.me/theorems/16c31511-7f63-40c8-ab4a-447896ea38e5
-- title:
--   ENSpec: emb smul
-- statement:
--   The ENSpec construction uses the emb smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L140-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L140-L149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))

theorem PIW.ENSpec.emb_smul (a : ℕ) (x : Fin D → R) (i : Fin D) (h : homogeneousSubmodule (Fin D) R a) :
    emb a ((-x i) • h) = (MvPolynomial.X i - MvPolynomial.C (x i)) • emb a h := by sorry
