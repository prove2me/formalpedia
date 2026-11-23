-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:51.402503+00:00
-- url     : https://prove2.me/theorems/e97234c1-ee00-4157-ae86-6b3d97b5f895
-- title:
--   P2 M Formalism Basic Notions Examples  NZ commute of single 11fa7f76e614: P2 M Formalism Basic Notions Examples  NZ commute of single 11fa7f76e614
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ commute of single 11fa7f76e614 construction uses the P2 M Formalism Basic Notions Examples  NZ commute of single 11fa7f76e614 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L60-L67

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614 {Γ : Type} [Group Γ] (z : MonoidAlgebra k Γ)
    (h : ∀ g : Γ, z * single g 1 = single g 1 * z) (a : MonoidAlgebra k Γ) : z * a = a * z := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«commute_of_single» := P2M_Formalism_BasicNotions_Examples__NZ_commute_of_single_11fa7f76e614
