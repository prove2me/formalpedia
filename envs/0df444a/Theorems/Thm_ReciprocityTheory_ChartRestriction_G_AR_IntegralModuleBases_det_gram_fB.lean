-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_det_gram_fB
-- name    : ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.det_gram_fB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:37.959788+00:00
-- url     : https://prove2.me/theorems/5153f466-e5fe-47c5-be64-35674c18a562
-- title:
--   Integral Module Bases: det gram f B
-- statement:
--   The Integral Module Bases construction uses the det gram f B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/DetToMatrixSq.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/DetToMatrixSq.lean#L30-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder
variable {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.det_gram_fB (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (Matrix.gram ℝ fun i => fB B (e i)).det = A.det := by sorry
