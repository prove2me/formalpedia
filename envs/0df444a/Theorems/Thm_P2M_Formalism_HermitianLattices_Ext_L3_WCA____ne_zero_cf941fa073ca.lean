-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:27:07.13155+00:00
-- url     : https://prove2.me/theorems/d461d3ab-5273-4316-b841-6096119aef68
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 WCA    ne zero cf941fa073ca: P2 M Formalism Hermitian Lattices Ext L3 WCA    ne zero cf941fa073ca
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 WCA    ne zero cf941fa073ca construction uses the P2 M Formalism Hermitian Lattices Ext L3 WCA    ne zero cf941fa073ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/InLZeroIff.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/InLZeroIff.lean#L27-L30

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca {t : 𝓞 F} (ht : t ≠ 0) : κ (ι t) ≠ 0 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«WCA».«κι_ne_zero» := P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
