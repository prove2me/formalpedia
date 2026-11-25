-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_beta_vanish
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.beta_vanish
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:25.245849+00:00
-- url     : https://prove2.me/theorems/8015212a-a7d5-5868-8271-bcdd13bee3bd
-- title:
--   ERam: beta vanish
-- statement:
--   The ERam construction uses the beta vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L162-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamCore.lean#L162-L234

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.beta_vanish (B : FB R d O) {Ty : Type} [Fintype Ty] (χ : Ty → O →+* k) (nt : Ty → ℕ)
    (bt : ∀ t, Fin (nt t) → O) (ct : ∀ t, Fin (nt t) → k) (heq : ∀ t, IsEqv (χ t) (bt t) (ct t))
    (hcompH : ∑ t, actD (EigA.dActH k B) (bt t) (ct t) = 1) (hcompS : ∑ t, actD (EigA.dActS k B) (bt t) (ct t) = 1)
    {n n' : ℕ} (bz : Fin n → O) (cz : Fin n → k) (bw : Fin n' → O) (cw : Fin n' → k) (ξ0 η0 : (Fin d → k) × (Fin d → k))
    (hsep : ∀ t t', evD (χ t) bz cz ≠ 0 → evD (χ t') bw cw ≠ 0 → ∃ a, χ t a ≠ χ t' (star a)) :
    betaH k (actP B bz cz ξ0) (actP B bw cw η0) = 0 := by sorry
