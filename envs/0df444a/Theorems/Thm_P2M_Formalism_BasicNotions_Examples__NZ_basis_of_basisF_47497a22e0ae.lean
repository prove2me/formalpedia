-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basisF_47497a22e0ae
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basisF_47497a22e0ae
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:34.89189+00:00
-- url     : https://prove2.me/theorems/c68a3cb9-5052-4977-82e2-b8d94937fc6c
-- title:
--   P2 M Formalism Basic Notions Examples  NZ basis of basis F 47497a22e0ae: P2 M Formalism Basic Notions Examples  NZ basis of basis F 47497a22e0ae
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ basis of basis F 47497a22e0ae construction uses the P2 M Formalism Basic Notions Examples  NZ basis of basis F 47497a22e0ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean#L73-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean#L73-L95

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF
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
open scoped TensorProduct nonZeroDivisors

theorem P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basisF_47497a22e0ae {K F W M ι κ : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module F M] [Fintype ι] [Fintype κ] (σ : K →+* F) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent F (fun i => e (b i)) ∧ Submodule.span F (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent F (fun i => e (b' i)) ∧ Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«basis_of_basisF» := P2M_Formalism_BasicNotions_Examples__NZ_basis_of_basisF_47497a22e0ae
