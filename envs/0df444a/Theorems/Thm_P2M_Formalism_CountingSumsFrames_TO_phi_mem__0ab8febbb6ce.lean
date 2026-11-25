-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_phi_mem__0ab8febbb6ce
-- name    : P2M_Formalism_CountingSumsFrames_TO_phi_mem__0ab8febbb6ce
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:32.57481+00:00
-- url     : https://prove2.me/theorems/8b5bcf9f-c921-4d85-b1ab-7ff02cae136b
-- title:
--   P2 M Formalism Counting Sums Frames TO phi mem  0ab8febbb6ce: P2 M Formalism Counting Sums Frames TO phi mem  0ab8febbb6ce
-- statement:
--   The P2 M Formalism Counting Sums Frames TO phi mem  0ab8febbb6ce construction uses the P2 M Formalism Counting Sums Frames TO phi mem  0ab8febbb6ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1498-L1507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1498-L1507

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_CountingSumsFrames_TO_phi_mem__0ab8febbb6ce (L : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p L j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by sorry

alias «Formalism».«CountingSumsFrames».«TO».«phi_mem'» := P2M_Formalism_CountingSumsFrames_TO_phi_mem__0ab8febbb6ce
