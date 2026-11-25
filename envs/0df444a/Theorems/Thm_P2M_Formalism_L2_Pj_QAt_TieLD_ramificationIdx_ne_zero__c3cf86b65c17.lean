-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_QAt_TieLD_ramificationIdx_ne_zero__c3cf86b65c17
-- name    : P2M_Formalism_L2_Pj_QAt_TieLD_ramificationIdx_ne_zero__c3cf86b65c17
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:34.097282+00:00
-- url     : https://prove2.me/theorems/0301e6a2-47b5-469a-b98a-d6f17bdab1bd
-- title:
--   P2 M Formalism L2 Pj QAt Tie LD ramification Idx ne zero  c3cf86b65c17: P2 M Formalism L2 Pj QAt Tie LD ramification Idx ne zero  c3cf86b65c17
-- statement:
--   The P2 M Formalism L2 Pj QAt Tie LD ramification Idx ne zero  c3cf86b65c17 construction uses the P2 M Formalism L2 Pj QAt Tie LD ramification Idx ne zero  c3cf86b65c17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L111-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
attribute [local instance] algCT
attribute [local instance] locT
attribute [local instance] dvrT
attribute [local instance] dvrLa
attribute [local instance] algLaK
attribute [local instance] towerLaK
attribute [local instance] fracLaK

theorem P2M_Formalism_L2_Pj_QAt_TieLD_ramificationIdx_ne_zero__c3cf86b65c17 (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by sorry

alias «Formalism».«L2».«Pj».«QAt».«TieLD».«ramificationIdx_ne_zero'» := P2M_Formalism_L2_Pj_QAt_TieLD_ramificationIdx_ne_zero__c3cf86b65c17
