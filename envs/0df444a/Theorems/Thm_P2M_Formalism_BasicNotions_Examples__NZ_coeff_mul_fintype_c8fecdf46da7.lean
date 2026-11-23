-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coeff_mul_fintype_c8fecdf46da7
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_coeff_mul_fintype_c8fecdf46da7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:46.275802+00:00
-- url     : https://prove2.me/theorems/11108f42-86ff-497d-915b-6de1142f263f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ coeff mul fintype c8fecdf46da7: P2 M Formalism Basic Notions Examples  NZ coeff mul fintype c8fecdf46da7
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ coeff mul fintype c8fecdf46da7 construction uses the P2 M Formalism Basic Notions Examples  NZ coeff mul fintype c8fecdf46da7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
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
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem P2M_Formalism_BasicNotions_Examples__NZ_coeff_mul_fintype_c8fecdf46da7 {Γ : Type} [Group Γ] [Fintype Γ] (x y : MonoidAlgebra k Γ) (g : Γ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«coeff_mul_fintype» := P2M_Formalism_BasicNotions_Examples__NZ_coeff_mul_fintype_c8fecdf46da7
