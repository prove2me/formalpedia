-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_core
-- name    : PositivityTheory.RgUd.T.Nil.BasePf.core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:50.315799+00:00
-- url     : https://prove2.me/theorems/89a54d35-f221-48be-87da-72db9cc0ea1e
-- title:
--   Base Pf: core
-- statement:
--   The Base Pf construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L79-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/BaseOrbits/PieceMem.lean#L79-L242

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
variable {ι : Type*}
open Classical

theorem PositivityTheory.RgUd.T.Nil.BasePf.core (hcomm : ∀ a b : G, a * b = b * a) (hcont : ∀ g : G, Continuous fun w : W => g • w)
    (D : (Y × W → ℂ) →ₗ[ℂ] ℂ)
    (hD : ∀ g : G, ∀ f ∈ TF (Y × W), D (fun p => f (p.1, g • p.2)) = D f)
    (S : Set W) (w0 : W) (htr : ∀ w ∈ S, ∃ g : G, g • w0 = w)
    (K : ι → Subgroup G) (hKo : ∀ i, ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K i, g • w = w'})
    (hKf : ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), ∃ i, ∀ g ∈ K i, ∀ p : Y × W, f (p.1, g • p.2) = f p)
    (t : G) (L : Set W) (hLc : IsCompact L) (hLo : IsOpen L) (hLK : ∀ i, ∀ g ∈ K i, ∀ w ∈ L, g • w ∈ L)
    (htL : ∀ w, t⁻¹ • w ∈ L → w ∈ L) (hLS : ∀ w ∈ L, t⁻¹ • w ∉ L → w ∈ S)
    (hne : ∃ w ∈ L, t⁻¹ • w ∉ L) :
    ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), D f = 0 := by sorry
