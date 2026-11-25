-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53
-- name    : P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:54.756784+00:00
-- url     : https://prove2.me/theorems/14b8baff-1ce7-462f-bf51-4cb05f6262d3
-- title:
--   P2 M Formalism Basic Notions Examples  CD coe phi 846279105f53: P2 M Formalism Basic Notions Examples  CD coe phi 846279105f53
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD coe phi 846279105f53 construction uses the P2 M Formalism Basic Notions Examples  CD coe phi 846279105f53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L62-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L62-L62

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

theorem P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53 (g : UpqT P Q) : coeMatrixAlt ε (phi ε e h1 h2 g) = Matrix.reindex e e (UpqT.mat g) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«coe_phi» := P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53
