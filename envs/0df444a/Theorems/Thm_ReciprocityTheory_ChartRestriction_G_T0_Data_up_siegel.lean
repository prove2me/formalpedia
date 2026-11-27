-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_up_siegel
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.up_siegel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:09:32.12457+00:00
-- url     : https://prove2.me/theorems/282ca941-f39c-5a84-84a6-48756d6f0111
-- title:
--   Data: up siegel
-- statement:
--   The Data construction uses the up siegel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpSiegel.lean#L19-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpSiegel.lean#L19-L151

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.up_siegel (hd : d.AxH 𝒜) (F1 : MvPolynomial (UXVar d.D d.N) K) (deF : ℕ)
    (h1 : 1 ≤ deF) (hle : deF ≤ d.del) (hirr : Irreducible F1) (hx : XHom deF F1)
    (hu : UDegLE ((d.D + 1) * d.del) F1) (hpos : 0 < hT F1) :
    ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K), XHom d.n96 (mapK Q) ∧ UDegLE d.n96' (mapK Q) ∧
      ¬ F1 ∣ mapK Q ∧
      meanK (fun σ => Real.log (qnorm σ F1 d.n96 d.n96' Q)) ≤
        -(d.n96 * hT F1 / ((d.D + 2) * deF)) +
          1 / 2 * Real.log (cardUX d.D d.N d.n96 d.n96') + d.PO := by sorry
