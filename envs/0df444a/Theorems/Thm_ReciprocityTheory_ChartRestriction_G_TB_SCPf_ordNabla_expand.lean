-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_ordNabla_expand
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_expand
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:16.324165+00:00
-- url     : https://prove2.me/theorems/a9befaa5-18c6-5842-b3b6-31569eca14fb
-- title:
--   SCPf: ord Nabla expand
-- statement:
--   The SCPf construction uses the ord Nabla expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaH.lean#L34-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaH.lean#L34-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_expand (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι π : Type}
    [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        nablaPoly k B h m u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) (liftX k g) := by sorry
