-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_exists_E__cec9a940fda7
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_HU_exists_E__cec9a940fda7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:09.994392+00:00
-- url     : https://prove2.me/theorems/044984d5-9fde-47b4-86c1-24d871658962
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 HU exists E  cec9a940fda7: P2 M Formalism Hermitian Lattices Ext L3 HU exists E  cec9a940fda7
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 HU exists E  cec9a940fda7 construction uses the P2 M Formalism Hermitian Lattices Ext L3 HU exists E  cec9a940fda7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeEqOfSymm.lean#L124-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeEqOfSymm.lean#L124-L146

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem P2M_Formalism_HermitianLattices_Ext_L3_HU_exists_E__cec9a940fda7 (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0)
    (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) :
    ∃ (E₀ : Matrix κ κ (𝓞 K)) (d : 𝓞 F), d ∉ 𝔭 ^ (e + 1) ∧ H * E₀ = ι d • (1 : Matrix κ κ (𝓞 K)) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«HU».«exists_E₀» := P2M_Formalism_HermitianLattices_Ext_L3_HU_exists_E__cec9a940fda7
