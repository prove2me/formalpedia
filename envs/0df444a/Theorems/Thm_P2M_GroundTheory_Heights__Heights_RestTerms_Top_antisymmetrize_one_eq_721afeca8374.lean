-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_one_eq_721afeca8374
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_one_eq_721afeca8374
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:35.942164+00:00
-- url     : https://prove2.me/theorems/b59fad82-a45e-4a38-ad30-d79534fee22d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize one eq 721afeca8374: P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize one eq 721afeca8374
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize one eq 721afeca8374 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize one eq 721afeca8374 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L97-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_one_eq_721afeca8374 (N : ℕ) (P : RootRing 1 N) :
    antisymmetrize 1 N P = ∑ v : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign v : ℤˣ) : ℤ) : ℚ) • blockPermute 1 N (fun _ => v) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«antisymmetrize_one_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_one_eq_721afeca8374
