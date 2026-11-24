-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_gs_fac
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.gs_fac
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:16:14.515796+00:00
-- url     : https://prove2.me/theorems/326d2c47-9018-4641-af0e-02660d1dfdbc
-- title:
--   GS: gs fac
-- statement:
--   The GS construction uses the gs fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L25-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L25-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.gs_fac (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : LinearIndependent ℂ w) :
    ∃ (u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ), Orthonormal ℂ u ∧
      τ.BlockTriangular id ∧ (∀ j, τ j j ≠ 0) ∧ (∀ a, w a = ∑ b, τ b a • u b) ∧
      ∀ a, u a ∈ Submodule.span ℂ (Set.range w) := by sorry
