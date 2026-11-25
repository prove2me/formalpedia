-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_symm_5fefe4430c04
-- name    : P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_symm_5fefe4430c04
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:48.445264+00:00
-- url     : https://prove2.me/theorems/01e0a579-3730-4b13-b1a2-b1219eaf3704
-- title:
--   P2 M Ground Theory Heights  Heights is Multi Homog relabel symm 5fefe4430c04: P2 M Ground Theory Heights  Heights is Multi Homog relabel symm 5fefe4430c04
-- statement:
--   The P2 M Ground Theory Heights  Heights is Multi Homog relabel symm 5fefe4430c04 construction uses the P2 M Ground Theory Heights  Heights is Multi Homog relabel symm 5fefe4430c04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L226-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L226-L238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_symm_5fefe4430c04 {g : MRing ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog ((relabelRingEquiv ε h).symm g) (fun k => d (ε k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isMultiHomog_relabel_symm» := P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_symm_5fefe4430c04
