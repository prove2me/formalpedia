-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_value_eq_fcf9e3525991
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_value_eq_fcf9e3525991
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:28.769511+00:00
-- url     : https://prove2.me/theorems/ba94a3e0-bf77-4e49-9bc9-4dd1df624eb0
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero value eq fcf9e3525991: P2 M Ground Theory Heights  Heights Proj Chow Nonzero value eq fcf9e3525991
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero value eq fcf9e3525991 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero value eq fcf9e3525991 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L133-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_value_eq_fcf9e3525991 {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) =
      toK e (aeval (locPar A) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«value_eq» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_value_eq_fcf9e3525991
