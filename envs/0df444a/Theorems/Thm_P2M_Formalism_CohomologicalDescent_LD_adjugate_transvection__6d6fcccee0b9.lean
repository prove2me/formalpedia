-- Prove2me | Theorems.Thm_P2M_Formalism_CohomologicalDescent_LD_adjugate_transvection__6d6fcccee0b9
-- name    : P2M_Formalism_CohomologicalDescent_LD_adjugate_transvection__6d6fcccee0b9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:35.704712+00:00
-- url     : https://prove2.me/theorems/22873719-4e86-45a1-aa4f-41ec080920c5
-- title:
--   P2 M Formalism Cohomological Descent LD adjugate transvection  6d6fcccee0b9: P2 M Formalism Cohomological Descent LD adjugate transvection  6d6fcccee0b9
-- statement:
--   The P2 M Formalism Cohomological Descent LD adjugate transvection  6d6fcccee0b9 construction uses the P2 M Formalism Cohomological Descent LD adjugate transvection  6d6fcccee0b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L789-L797
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L789-L797

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem P2M_Formalism_CohomologicalDescent_LD_adjugate_transvection__6d6fcccee0b9 {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n] (i j : n)
    (h : i ≠ j) (c : S) : (Matrix.transvection i j c).adjugate = Matrix.transvection i j (-c) := by sorry

alias «Formalism».«CohomologicalDescent».«LD».«adjugate_transvection'» := P2M_Formalism_CohomologicalDescent_LD_adjugate_transvection__6d6fcccee0b9
