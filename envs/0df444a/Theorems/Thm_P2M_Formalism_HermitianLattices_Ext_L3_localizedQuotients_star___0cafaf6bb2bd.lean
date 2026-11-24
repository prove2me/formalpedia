-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:00.962788+00:00
-- url     : https://prove2.me/theorems/a566531f-41a7-46ee-91fc-2c9295131a78
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 localized Quotients star   0cafaf6bb2bd: P2 M Formalism Hermitian Lattices Ext L3 localized Quotients star   0cafaf6bb2bd
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 localized Quotients star   0cafaf6bb2bd construction uses the P2 M Formalism Hermitian Lattices Ext L3 localized Quotients star   0cafaf6bb2bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L89-L91

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd (hF : IsFixF K F) (a : 𝓞 F) :
    star (algebraMap (𝓞 K) K (ι a)) = algebraMap (𝓞 K) K (ι a) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«localizedQuotients».«star_ι» := P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd
