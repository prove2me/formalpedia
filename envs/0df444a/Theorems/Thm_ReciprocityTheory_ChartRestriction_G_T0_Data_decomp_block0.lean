-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_decomp_block0
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.decomp_block0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:26:24.187527+00:00
-- url     : https://prove2.me/theorems/886cf85f-6ead-5900-8e2e-fdf9b0f208b9
-- title:
--   Data: decomp block0
-- statement:
--   The Data construction uses the decomp block0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DecompBlock0.lean#L66-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DecompBlock0.lean#L66-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
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
set_option synthInstance.maxHeartbeats 400000

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.decomp_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ (L E : Type) (_ : Field L) (_ : Field E) (_ : Algebra L E) (_ : FiniteDimensional L E)
      (eL : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (eE : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) E)),
      (∀ q : KTf K d.D d.N, eE (d.KTtoS h c q) = VariableBasisExtension.liftY (eL q)) ∧
      (∀ r : Ω c, ∃ e : E, eE (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap (MvPolynomial (Fin (d.N + 1)) E) (FractionRing (MvPolynomial (Fin (d.N + 1)) E))
          (MvPolynomial.C e)) ∧
      ∀ l : L, ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x P = P) ∧ (∀ x, d.sub0 x Q = Q) ∧
        eL.symm (algebraMap (MvPolynomial (Fin (d.N + 1)) L)
            (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (MvPolynomial.C l)) =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q := by sorry
