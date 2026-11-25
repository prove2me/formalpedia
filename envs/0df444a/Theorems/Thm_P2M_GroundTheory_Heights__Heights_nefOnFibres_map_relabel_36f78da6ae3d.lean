-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_nefOnFibres_map_relabel_36f78da6ae3d
-- name    : P2M_GroundTheory_Heights__Heights_nefOnFibres_map_relabel_36f78da6ae3d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:26.469799+00:00
-- url     : https://prove2.me/theorems/a7a18871-6d1e-4757-b746-a51e4c1b1a71
-- title:
--   P2 M Ground Theory Heights  Heights nef On Fibres map relabel 36f78da6ae3d: P2 M Ground Theory Heights  Heights nef On Fibres map relabel 36f78da6ae3d
-- statement:
--   The P2 M Ground Theory Heights  Heights nef On Fibres map relabel 36f78da6ae3d construction uses the P2 M Ground Theory Heights  Heights nef On Fibres map relabel 36f78da6ae3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L364-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L364-L381

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

theorem P2M_GroundTheory_Heights__Heights_nefOnFibres_map_relabel_36f78da6ae3d (P : Ideal (MRing ι)) (a : K' → ℤ) :
    NefOnFibres P (a ∘ ε) ↔ NefOnFibres (P.map (relabelRingEquiv ε h)) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«nefOnFibres_map_relabel» := P2M_GroundTheory_Heights__Heights_nefOnFibres_map_relabel_36f78da6ae3d
