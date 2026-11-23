-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:02.272428+00:00
-- url     : https://prove2.me/theorems/6bb6e04c-db96-4b4c-ada5-9b2c37fdb4e1
-- title:
--   P2 M Formalism Basic Notions Examples  NZ tens coeff b71da958868c: P2 M Formalism Basic Notions Examples  NZ tens coeff b71da958868c
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ tens coeff b71da958868c construction uses the P2 M Formalism Basic Notions Examples  NZ tens coeff b71da958868c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L14-L15

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c (x : ∀ i, MonoidAlgebra k (G i)) (g : ∀ i, G i) :
    (tens x).coeff g = ∏ i, (x i).coeff (g i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«tens_coeff» := P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c
