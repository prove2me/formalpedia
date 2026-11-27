-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_up_cauchy
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.up_cauchy
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T05:16:41.180069+00:00
-- url     : https://prove2.me/theorems/2c421f70-d13a-5731-8f77-e7381e20f744
-- title:
--   Data: up cauchy
-- statement:
--   The Data construction uses the up cauchy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormLineSectionPow.lean#L105-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormLineSectionPow.lean#L105-L295

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.up_cauchy (hd : d.AxH 𝒜) (hdel : 1 ≤ d.del) (c : ι) (F1 : MvPolynomial (UXVar d.D d.N) K)
    (deF : ℕ) (hxF : XHom deF F1)
    (hker : ∀ (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K), XHom n Q → (d.evc c Q = 0 ↔ F1 ∣ Q))
    (Q : MvPolynomial (UXVar d.D d.N) (𝓞 K)) (hQx : XHom d.n96 (mapK Q))
    (hQu : UDegLE d.n96' (mapK Q)) (hQ : ¬ F1 ∣ mapK Q) :
    ∃ g ∈ Submodule.span (𝓞 K)
        (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 ∧
      meanK (fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c))) ≤
        meanK (fun σ => Real.log (qnorm σ F1 d.n96 d.n96' Q)) +
          1 / 2 * Real.log (cardUX d.D d.N d.n96 d.n96') +
          d.n96 * (d.laW + Real.log (d.N + 1 : ℕ)) := by sorry
