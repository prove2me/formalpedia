-- Prove2me | Theorems.Thm_PositivityTheory_KCo_top_of_map
-- name    : PositivityTheory.KCo.top_of_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:32.39198+00:00
-- url     : https://prove2.me/theorems/41a97464-7e6a-47cd-9699-6e1b712a58c4
-- title:
--   KCo: top of map
-- statement:
--   The KCo construction uses the top of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/TopOfMap.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/TopOfMap.lean#L15-L23

import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.KCo.top_of_map {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (Φ : V →ₗ[ℂ] U) {R N : Submodule ℂ V}
    (hK : ∀ f, Φ f = 0 → f ∈ R) (hR : R ≤ N) (h : N.map Φ = ⊤) : N = ⊤ := by sorry
