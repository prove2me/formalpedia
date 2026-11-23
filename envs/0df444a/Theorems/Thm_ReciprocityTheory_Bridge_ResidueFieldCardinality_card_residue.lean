-- Prove2me | Theorems.Thm_ReciprocityTheory_Bridge_ResidueFieldCardinality_card_residue
-- name    : ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:02.109841+00:00
-- url     : https://prove2.me/theorems/03175278-b5fa-484b-8a59-8129bbb6ab4e
-- title:
--   Residue Field Cardinality: card residue
-- statement:
--   The Residue Field Cardinality construction uses the card residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ResidueCardinality/ArtinOntoB.lean#L14-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ResidueCardinality/ArtinOntoB.lean#L14-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Bridge ReciprocityTheory.Bridge.ResidueFieldCardinality
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
set_option maxHeartbeats 800000

theorem ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Nat.card (𝓞 F ⧸ v.asIdeal) := by sorry
