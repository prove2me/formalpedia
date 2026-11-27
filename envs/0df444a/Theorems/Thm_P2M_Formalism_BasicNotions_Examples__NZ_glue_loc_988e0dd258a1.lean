-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_glue_loc_988e0dd258a1
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_glue_loc_988e0dd258a1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:19.925715+00:00
-- url     : https://prove2.me/theorems/be72041f-15df-5984-b712-f014d27e303e
-- title:
--   P2 M Formalism Basic Notions Examples  NZ glue loc 988e0dd258a1: P2 M Formalism Basic Notions Examples  NZ glue loc 988e0dd258a1
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ glue loc 988e0dd258a1 construction uses the P2 M Formalism Basic Notions Examples  NZ glue loc 988e0dd258a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZColB.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZColB.lean#L19-L36

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZColB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]

theorem P2M_Formalism_BasicNotions_Examples__NZ_glue_loc_988e0dd258a1 (A : HeightOneSpectrum R → Submodule R V)
    (hsat : ∀ w (s : R), s ∉ w.asIdeal → ∀ x, s • x ∈ A w → x ∈ A w)
    (hfin : ∀ x : V, {w | x ∉ A w}.Finite)
    (habs : ∀ w (x : V), ∃ m : ℕ, ∀ a ∈ w.asIdeal ^ m, a • x ∈ A w)
    (w : HeightOneSpectrum R) (x : V) :
    (∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ glue A) ↔ x ∈ A w := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«glue_loc» := P2M_Formalism_BasicNotions_Examples__NZ_glue_loc_988e0dd258a1
