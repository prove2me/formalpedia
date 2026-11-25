-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_exists_frac_b1f380c0d544
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_exists_frac_b1f380c0d544
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:53.79753+00:00
-- url     : https://prove2.me/theorems/6d0b068e-a541-4fcd-9580-5e0a17b4fe6a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact exists frac b1f380c0d544: P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact exists frac b1f380c0d544
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact exists frac b1f380c0d544 construction uses the P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact exists frac b1f380c0d544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L45-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
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
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.DegLocExact
variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_exists_frac_b1f380c0d544 (𝓜 : GradedPMod S N M) (c : ℤ) (I : StdCell N) (z : LocMod S N M I.1)
    (hz : z ∈ degLoc 𝓜 c I) :
    ∃ (m : M) (s : monos (S := S) I.1) (e : ℕ), (s : Poly S N).IsHomogeneous e ∧
      m ∈ 𝓜.piece (c + e) ∧ z = (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DegLocExact».«exists_frac» := P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_exists_frac_b1f380c0d544
