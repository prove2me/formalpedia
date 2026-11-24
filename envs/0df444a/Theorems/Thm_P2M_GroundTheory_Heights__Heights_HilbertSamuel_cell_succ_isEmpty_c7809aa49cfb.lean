-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:26.470033+00:00
-- url     : https://prove2.me/theorems/09d54921-4e52-46d3-86fe-54cc957bbaff
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel cell succ is Empty c7809aa49cfb: P2 M Ground Theory Heights  Heights Hilbert Samuel cell succ is Empty c7809aa49cfb
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel cell succ is Empty c7809aa49cfb construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel cell succ is Empty c7809aa49cfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L39-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb (n : ℕ) : IsEmpty (KH.Cell K ι (n + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«cell_succ_isEmpty» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb
