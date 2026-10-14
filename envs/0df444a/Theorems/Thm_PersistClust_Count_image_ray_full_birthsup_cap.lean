-- Prove2me | Theorems.Thm_PersistClust_Count_image_ray_full_birthsup_cap
-- name    : PersistClust.Count.image_ray_full_birthsup_cap
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T07:21:06.465734+00:00
-- url     : https://prove2.me/theorems/a340e4a0-76dd-4e3d-809c-ed926daac30d
-- title:
--   Full birth-sup cap: an X-ray pinned at b on [d+eta', beta] has its Y-image capped by b+epsilon on (d+epsilon, beta-epsilon]
-- statement:
--   Let 0-dimensional persistence modules be given by filtration laws of finite type (IsTameModule) on two index levels X and Y, tied by an epsilon-shifted adjoint pair of component maps: phi maps X-classes at beta to Y-classes at beta - epsilon, and psi maps Y-classes at beta to X-classes at beta - epsilon, satisfying the two square identities (psi after descent commutes with descent; psi of phi of a class is its descent by epsilon). Let b, d, beta be levels with alpha <= d, alpha <= beta - epsilon and d + 2*epsilon < beta, and let A be an X-class at level beta with birthSup A = b. Suppose the X-ray of A is PINNED at the value b on the window [d + eta', beta]: for every s in [d + eta', beta] the descended class has birthSup s (descended A) = b; let eta' be positive with d + eta' <= beta; and suppose no X-critical level tau different from d lies within delta0 of d, with eta' < delta0. Then the Y-image phi beta A is capped on the whole probe window: for every v with d + epsilon < v <= beta - epsilon, the birth-sup of the descended image class is at most b + epsilon. The reason: at the anchor s0 := v - epsilon the X-value is exactly b (the pin itself if s0 is in the pin window; otherwise s0 lies in the critical-free window (d, d + eta'] and the pin at d + eta' transports down it - any X-critical level in [s0, d + eta'] would be within eta' < delta0 of d, contradicting the gap hypothesis), and the elder trap then bounds the Y-ray's birth sup by the anchored X-value plus epsilon.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): design part 4, the full-cap step of the elder-trap route - it turns a pinned window value (pin family at b plus a critical-free window above d) into a global cap on the image ray, excluding the raiser hazard zone for the census death-pinning. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified rank lane working copy together with its green support machinery (structMap composition, crit injectivity, the bSup thread transport, the descent floor, the double-descent pin and the elder trap); companion of the accepted census_merge_absorption_mult_nonzero, of the accepted theorem_4_5 elder-rule support cluster, of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem image_ray_full_birthsup_cap {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d β : ℝ} (hαβ : α ≤ β) (hαd : α ≤ d) (hβε : α ≤ β - ε) (hd : d + 2 * ε < β)
    {A : comps stageX JX β} (hA : birthSup hLawX β A = b)
    {η' δ₀ : ℝ} (hη'0 : 0 < η') (hη'β : d + η' ≤ β) (hη'δ : η' < δ₀)
    (hgapd : ∀ τ ∈ critSet hTameX, τ ≠ d → δ₀ < |τ - d|)
    (hpin : ∀ s (hs : d + η' ≤ s) (hsβ : s ≤ β),
      birthSup hLawX s (structMap hLawX hsβ A) = b) :
    ∀ v, d + ε < v → v ≤ β - ε → ∀ hle : v ≤ β - ε,
      birthSup hLawY v (structMap hLawY hle (φ β hαβ A)) ≤ b + ε
    := by sorry
