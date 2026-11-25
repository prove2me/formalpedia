-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_norm_th_lt
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.norm_th_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:12.020882+00:00
-- url     : https://prove2.me/theorems/37b3aea9-d9ce-424a-9584-70e76a586f27
-- title:
--   Fourier Coefficient Lattice: norm th lt
-- statement:
--   The Fourier Coefficient Lattice construction uses the norm th lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L29-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean#L29-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.norm_th_lt {y : ι → Fin 2 → Fin 2 → ℝ} (hy : ‖y‖ < 1) (τ : ι) (i k : Fin 2) :
    ‖th y τ i k‖ < 2 := by sorry
