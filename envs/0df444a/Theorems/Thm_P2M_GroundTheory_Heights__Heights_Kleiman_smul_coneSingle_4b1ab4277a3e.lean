-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:33.67839+00:00
-- url     : https://prove2.me/theorems/bc89c5d1-0e30-4a05-9a01-6f9c56b775f8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman smul cone Single 4b1ab4277a3e: P2 M Ground Theory Heights  Heights Kleiman smul cone Single 4b1ab4277a3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman smul cone Single 4b1ab4277a3e construction uses the P2 M Ground Theory Heights  Heights Kleiman smul cone Single 4b1ab4277a3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L117-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable (x : Fin (N + 1) → Ω)
variable {S x}
variable (S x)
variable {S x}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : ℤ) (v : Ω) :
    f • coneSingle S x c v = coneSingle S x (c + e) (aeval x f * v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«smul_coneSingle» := P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e
