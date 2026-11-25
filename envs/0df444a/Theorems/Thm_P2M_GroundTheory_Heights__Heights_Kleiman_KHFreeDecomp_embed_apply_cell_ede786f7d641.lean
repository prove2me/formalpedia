-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_embed_apply_cell_ede786f7d641
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_embed_apply_cell_ede786f7d641
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:17.632733+00:00
-- url     : https://prove2.me/theorems/81a8cdeb-e66e-44e8-b438-07c6e69f4b74
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp embed apply cell ede786f7d641: P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp embed apply cell ede786f7d641
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp embed apply cell ede786f7d641 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp embed apply cell ede786f7d641 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L116-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L116-L124

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_embed_apply_cell_ede786f7d641 [LinearOrder K] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ) (n : ℕ)
    (F : KH.Cell K ι n → S) (I : KH.Cell K ι n) :
    embed S a n (fun J => F J.1) I = F I • monoFrac S I.1 a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeDecomp».«embed_apply_cell» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_embed_apply_cell_ede786f7d641
