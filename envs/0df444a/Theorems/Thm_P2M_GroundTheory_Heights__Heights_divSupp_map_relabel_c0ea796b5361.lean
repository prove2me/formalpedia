-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_divSupp_map_relabel_c0ea796b5361
-- name    : P2M_GroundTheory_Heights__Heights_divSupp_map_relabel_c0ea796b5361
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:17.138853+00:00
-- url     : https://prove2.me/theorems/2a4204fa-8fad-47c2-82cb-6a87c101ebcb
-- title:
--   P2 M Ground Theory Heights  Heights div Supp map relabel c0ea796b5361: P2 M Ground Theory Heights  Heights div Supp map relabel c0ea796b5361
-- statement:
--   The P2 M Ground Theory Heights  Heights div Supp map relabel c0ea796b5361 construction uses the P2 M Ground Theory Heights  Heights div Supp map relabel c0ea796b5361 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L270-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L270-L282

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

theorem P2M_GroundTheory_Heights__Heights_divSupp_map_relabel_c0ea796b5361 (V : Ideal (MRing ι)) (s : MRing ι) :
    divSupp (V.map (relabelRingEquiv ε h)) (relabelRingEquiv ε h s) =
      Ideal.map (relabelRingEquiv ε h) '' divSupp V s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«divSupp_map_relabel» := P2M_GroundTheory_Heights__Heights_divSupp_map_relabel_c0ea796b5361
