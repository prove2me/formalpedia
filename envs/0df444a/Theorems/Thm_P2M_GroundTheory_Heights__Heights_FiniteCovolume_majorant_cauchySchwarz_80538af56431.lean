-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_cauchySchwarz_80538af56431
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_cauchySchwarz_80538af56431
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:44:21.765533+00:00
-- url     : https://prove2.me/theorems/a7ae4139-7686-4856-906c-5784603e62f9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume majorant cauchy Schwarz 80538af56431: P2 M Ground Theory Heights  Heights Finite Covolume majorant cauchy Schwarz 80538af56431
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume majorant cauchy Schwarz 80538af56431 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume majorant cauchy Schwarz 80538af56431 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenCauchySchwarz.lean#L15-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenCauchySchwarz.lean#L15-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenCauchySchwarz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_cauchySchwarz_80538af56431 {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (H *ᵥ b)‖ ≤
      Real.sqrt (star a ⬝ᵥ (P *ᵥ a)).re * Real.sqrt (star b ⬝ᵥ (P *ᵥ b)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«majorant_cauchySchwarz» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_cauchySchwarz_80538af56431
