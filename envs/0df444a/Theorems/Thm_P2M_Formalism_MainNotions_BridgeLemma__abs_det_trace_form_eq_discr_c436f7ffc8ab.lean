-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__abs_det_trace_form_eq_discr_c436f7ffc8ab
-- name    : P2M_Formalism_MainNotions_BridgeLemma__abs_det_trace_form_eq_discr_c436f7ffc8ab
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:18.223933+00:00
-- url     : https://prove2.me/theorems/7d86958a-318d-45b9-b2f0-78b265dda4ed
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  abs det trace form eq discr c436f7ffc8ab: P2 M Formalism Main Notions Bridge Lemma  abs det trace form eq discr c436f7ffc8ab
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  abs det trace form eq discr c436f7ffc8ab construction uses the P2 M Formalism Main Notions Bridge Lemma  abs det trace form eq discr c436f7ffc8ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L31-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L31-L68

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_MainNotions_BridgeLemma__abs_det_trace_form_eq_discr_c436f7ffc8ab (hK : IsCMUnram K) :
    |(Matrix.of fun j j' : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)).det| = |(discr K : ℝ)| := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«abs_det_trace_form_eq_discr» := P2M_Formalism_MainNotions_BridgeLemma__abs_det_trace_form_eq_discr_c436f7ffc8ab
