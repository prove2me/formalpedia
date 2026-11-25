-- Prove2me | Theorems.Thm_PositivityTheory_KCo_irr_ind
-- name    : PositivityTheory.KCo.irr_ind
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:18.698798+00:00
-- url     : https://prove2.me/theorems/519c24ba-142b-5575-85ae-9c1dde2d09d7
-- title:
--   KCo: irr ind
-- statement:
--   The KCo construction uses the irr ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/TopOfMap.lean#L96-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/TopOfMap.lean#L96-L139

import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two

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

theorem PositivityTheory.KCo.irr_ind (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp ((fibRep (Fin n) (Fin n) (Fin t) μ n).comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n) (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 := by sorry
