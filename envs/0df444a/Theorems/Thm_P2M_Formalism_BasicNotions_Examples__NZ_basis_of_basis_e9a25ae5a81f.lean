-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basis_e9a25ae5a81f
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basis_e9a25ae5a81f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:20.517073+00:00
-- url     : https://prove2.me/theorems/225f51c8-4cec-4e5a-a5a0-fe54bd641161
-- title:
--   P2 M Formalism Basic Notions Examples  NZ basis of basis e9a25ae5a81f: P2 M Formalism Basic Notions Examples  NZ basis of basis e9a25ae5a81f
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ basis of basis e9a25ae5a81f construction uses the P2 M Formalism Basic Notions Examples  NZ basis of basis e9a25ae5a81f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L220-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L220-L246

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions

theorem P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basis_e9a25ae5a81f {K W M ι κ : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module ℂ M] [Fintype ι] [Fintype κ] (σ : K →+* ℂ) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent ℂ (fun i => e (b i)) ∧ Submodule.span ℂ (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent ℂ (fun i => e (b' i)) ∧ Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«basis_of_basis» := P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basis_e9a25ae5a81f
