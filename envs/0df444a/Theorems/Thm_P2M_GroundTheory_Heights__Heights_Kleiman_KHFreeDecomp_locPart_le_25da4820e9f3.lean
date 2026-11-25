-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_locPart_le_25da4820e9f3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_locPart_le_25da4820e9f3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:35:46.003802+00:00
-- url     : https://prove2.me/theorems/499d6ffc-07fa-5ae7-b33b-ff8d332309b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp loc Part le 25da4820e9f3: P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp loc Part le 25da4820e9f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp loc Part le 25da4820e9f3 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp loc Part le 25da4820e9f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L72-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L72-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_locPart_le_25da4820e9f3 (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeDecomp».«locPart_le» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_locPart_le_25da4820e9f3
