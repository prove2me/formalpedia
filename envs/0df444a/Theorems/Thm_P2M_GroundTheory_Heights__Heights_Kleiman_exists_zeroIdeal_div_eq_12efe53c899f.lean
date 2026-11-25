-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_zeroIdeal_div_eq_12efe53c899f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_zeroIdeal_div_eq_12efe53c899f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:24.175168+00:00
-- url     : https://prove2.me/theorems/a445b7ba-69ba-4419-a61e-3dc0a669605b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists zero Ideal div eq 12efe53c899f: P2 M Ground Theory Heights  Heights Kleiman exists zero Ideal div eq 12efe53c899f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists zero Ideal div eq 12efe53c899f construction uses the P2 M Ground Theory Heights  Heights Kleiman exists zero Ideal div eq 12efe53c899f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutZeroNotLe.lean#L19-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutZeroNotLe.lean#L19-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutZeroNotLeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_zeroIdeal_div_eq_12efe53c899f (D : SubFamily S x Ω) (hfg : ∀ K, (D.sub K).FG) (I : Chart x)
    {σ y : Ω} (hσ : σ ∈ D.sub I) (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∃ (g t : Poly S N) (n : ℕ), g ∈ zeroIdeal D.toSubSystem σ ∧ t ∈ monos I.1 ∧
      g.IsHomogeneous n ∧ t.IsHomogeneous n ∧ σ * y = aeval x g / aeval x t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_zeroIdeal_div_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_zeroIdeal_div_eq_12efe53c899f
