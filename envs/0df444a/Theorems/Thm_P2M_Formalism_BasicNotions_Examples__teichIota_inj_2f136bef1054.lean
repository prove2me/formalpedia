-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__teichIota_inj_2f136bef1054
-- name    : P2M_Formalism_BasicNotions_Examples__teichIota_inj_2f136bef1054
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:04.633299+00:00
-- url     : https://prove2.me/theorems/fef01d56-edfe-4a59-90cb-bbf112c555e4
-- title:
--   P2 M Formalism Basic Notions Examples  teich Iota inj 2f136bef1054: P2 M Formalism Basic Notions Examples  teich Iota inj 2f136bef1054
-- statement:
--   The P2 M Formalism Basic Notions Examples  teich Iota inj 2f136bef1054 construction uses the P2 M Formalism Basic Notions Examples  teich Iota inj 2f136bef1054 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L219-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L219-L231

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Cardinal
variable (g l : ℕ) [Fact g.Prime] [Fact l.Prime]

theorem P2M_Formalism_BasicNotions_Examples__teichIota_inj_2f136bef1054 (x y : AlgebraicClosure (ZMod g)) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxl : (orderOf x).Coprime l) (hyl : (orderOf y).Coprime l)
    (h : teichIota g l x = teichIota g l y) : x = y := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«teichIota_inj» := P2M_Formalism_BasicNotions_Examples__teichIota_inj_2f136bef1054
