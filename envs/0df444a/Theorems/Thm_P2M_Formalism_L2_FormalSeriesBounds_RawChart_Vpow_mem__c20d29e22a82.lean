-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_RawChart_Vpow_mem__c20d29e22a82
-- name    : P2M_Formalism_L2_FormalSeriesBounds_RawChart_Vpow_mem__c20d29e22a82
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:12.510035+00:00
-- url     : https://prove2.me/theorems/272f8b36-21c0-42ff-9ac8-9d6a93498369
-- title:
--   P2 M Formalism L2 Formal Series Bounds Raw Chart Vpow mem  c20d29e22a82: P2 M Formalism L2 Formal Series Bounds Raw Chart Vpow mem  c20d29e22a82
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds Raw Chart Vpow mem  c20d29e22a82 construction uses the P2 M Formalism L2 Formal Series Bounds Raw Chart Vpow mem  c20d29e22a82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L77-L81

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem P2M_Formalism_L2_FormalSeriesBounds_RawChart_Vpow_mem__c20d29e22a82 (V : VF C) (g : Fin 2) (s : ℕ) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow s x ∈ X.TySet V g := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«RawChart».«Vpow_mem'» := P2M_Formalism_L2_FormalSeriesBounds_RawChart_Vpow_mem__c20d29e22a82
