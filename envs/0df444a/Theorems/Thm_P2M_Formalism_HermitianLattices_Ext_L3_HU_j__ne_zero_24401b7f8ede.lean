-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:56.421516+00:00
-- url     : https://prove2.me/theorems/0393047f-4aba-4fe8-a049-fedbc06a06dc
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 HU j  ne zero 24401b7f8ede: P2 M Formalism Hermitian Lattices Ext L3 HU j  ne zero 24401b7f8ede
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 HU j  ne zero 24401b7f8ede construction uses the P2 M Formalism Hermitian Lattices Ext L3 HU j  ne zero 24401b7f8ede property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeZeroOfNotMem.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeZeroOfNotMem.lean#L26-L33

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«HU».«jι_ne_zero» := P2M_Formalism_HermitianLattices_Ext_L3_HU_j__ne_zero_24401b7f8ede
