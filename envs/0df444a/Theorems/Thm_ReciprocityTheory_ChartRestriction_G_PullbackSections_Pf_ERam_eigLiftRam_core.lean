-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_eigLiftRam_core
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eigLiftRam_core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:02.256818+00:00
-- url     : https://prove2.me/theorems/6662f844-3013-59ef-bdb7-095fbf1c0059
-- title:
--   ERam: eig Lift Ram core
-- statement:
--   The ERam construction uses the eig Lift Ram core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamLift.lean#L90-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamLift.lean#L90-L232

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamLift
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eigLiftRam_core (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h)
    {L Ty Pl π : Type} [Fintype Ty] (ty : L → Ty) (χ : Ty → O →+* k) (cjT : Ty → Ty)
    (hχsep : ∀ t t', t' ≠ cjT t → ∃ a, χ t a ≠ χ t' (star a)) (hχinj : ∀ t t', t ≠ t' → ∃ a, χ t a ≠ χ t' a)
    (u : L → Fin d → R)
    (heig : ∀ ℓ a, (dAct k B a).mulVec (fun i => algebraMap R k (u ℓ i)) = χ (ty ℓ) a • fun i => algebraMap R k (u ℓ i))
    (nt : Ty → ℕ) (bt : ∀ t, Fin (nt t) → O) (ct : ∀ t, Fin (nt t) → k) (heqt : ∀ t, IsEqv (χ t) (bt t) (ct t))
    (hcompH : ∑ t, actD (EigA.dActH k B) (bt t) (ct t) = 1) (hcompS : ∑ t, actD (EigA.dActS k B) (bt t) (ct t) = 1)
    (pl : Ty → Pl) (cjP : Pl → Pl) (hpl : ∀ t, pl (cjT t) = cjP (pl t))
    (nP : Pl → ℕ) (bP : ∀ w, Fin (nP w) → O) (aP : ∀ w, Fin (nP w) → R)
    (hP : ∀ w t, evD (χ t) (bP w) (fun i => algebraMap R k (aP w i)) = if pl t = w then 1 else 0)
    (nE : Ty → ℕ) (bE : ∀ t, Fin (nE t) → O) (cE : ∀ t, Fin (nE t) → k) (heqE : ∀ t, IsEqv (χ t) (bE t) (cE t))
    (hnE : ∀ t, evD (χ t) (bE t) (cE t) = 1) (r : Ty → R)
    (hr : ∀ t i, ∃ v : R, algebraMap R k v = algebraMap R k (r t) * cE t i)
    (c : Ty → π) (s : Ty → Bool) (hpair : ∀ t t', pl t' = cjP (pl t) → c t = c t' ∧ s t ≠ s t') :
    ∃ (φ : L → Fin d → R) (ψ : L → Fin d → k),
      (∀ ℓ i, algebraMap R k (r (ty ℓ)) * ψ ℓ i ∈ (algebraMap R k).range) ∧
      (∀ ℓ ℓ', ty ℓ' ≠ cjT (ty ℓ) →
        ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
          algebraMap R k (u ℓ i) = 0) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ)) (fun ℓ => (0, ψ ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
        (fun ℓ => (0, ψ ℓ)) := by sorry
