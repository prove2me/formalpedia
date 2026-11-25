-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_rep_iff_6121dedef159
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_rep_iff_6121dedef159
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:32.227534+00:00
-- url     : https://prove2.me/theorems/8ee41dfd-8060-4c42-9c9a-0911883827ad
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates rep iff 6121dedef159: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates rep iff 6121dedef159
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates rep iff 6121dedef159 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates rep iff 6121dedef159 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L120-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_rep_iff_6121dedef159 (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') {dg dh : Unit → ℕ} {g h : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) :
    aeval x g = μ ^ ((τ : ℤ) * A.a ()) * j s' * aeval x h ↔ aeval y g = s' * aeval y h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«rep_iff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_rep_iff_6121dedef159
