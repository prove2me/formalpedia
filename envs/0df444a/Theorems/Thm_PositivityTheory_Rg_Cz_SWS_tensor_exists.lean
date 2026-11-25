-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SWS_tensor_exists
-- name    : PositivityTheory.Rg.Cz.SWS.tensor_exists
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:28.167348+00:00
-- url     : https://prove2.me/theorems/da1b110e-4eab-52d2-8edf-827621a38678
-- title:
--   SWS: tensor exists
-- statement:
--   The SWS construction uses the tensor exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStart.lean#L76-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStart.lean#L76-L110

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.SWS.tensor_exists [IsTopologicalGroup Γ] [μ.IsMulLeftInvariant] {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (y : M) {m : ℕ} (lab : Fin m → ι)
    (c : ι → ℤ) (K : Fin m → Fin n) :
    ∃ ξ : TV n M (Fin m), (∀ γ, actT lab κ ρ γ ξ = (∏ τ, (κ τ γ).det ^ (-c τ)) • ξ) ∧
      ∀ I (lam : M →ₗ[ℂ] ℂ), lam (ξ I) = ∫ k, mono κ lab c I K k * lam (ρ k y) ∂μ := by sorry
