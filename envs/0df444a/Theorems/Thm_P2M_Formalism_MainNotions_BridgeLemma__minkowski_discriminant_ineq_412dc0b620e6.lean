-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__minkowski_discriminant_ineq_412dc0b620e6
-- name    : P2M_Formalism_MainNotions_BridgeLemma__minkowski_discriminant_ineq_412dc0b620e6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:21.096338+00:00
-- url     : https://prove2.me/theorems/1108467d-f6d4-460d-b5af-d04a62dc3829
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  minkowski discriminant ineq 412dc0b620e6: P2 M Formalism Main Notions Bridge Lemma  minkowski discriminant ineq 412dc0b620e6
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  minkowski discriminant ineq 412dc0b620e6 construction uses the P2 M Formalism Main Notions Bridge Lemma  minkowski discriminant ineq 412dc0b620e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L228-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L228-L250

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
open MeasureTheory

theorem P2M_Formalism_MainNotions_BridgeLemma__minkowski_discriminant_ineq_412dc0b620e6 (n : ℕ) (hn : 1 ≤ n) (Δ rd : ℝ) (hΔ : 0 < Δ) (hrd : rd ^ n = Δ) (hrd0 : 0 < rd) :
    Δ * 2 ^ (2 * n) < Real.sqrt (2 * n * rd) ^ (2 * n) * (√Real.pi ^ (2 * n) / Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1)) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«minkowski_discriminant_ineq» := P2M_Formalism_MainNotions_BridgeLemma__minkowski_discriminant_ineq_412dc0b620e6
