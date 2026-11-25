-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kHom
-- name    : PositivityTheory.Rg.Cz.kHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:53.938325+00:00
-- url     : https://prove2.me/theorems/4f36c3ab-e959-4329-9cb4-aa0bec6cdfe4
-- title:
--   Cz: k Hom
-- statement:
--   The Cz construction uses the k Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L34-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L34-L99

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem PositivityTheory.Rg.Cz.kHom {β γ : Type} [Fintype β] [Fintype γ] (b : β → P) (a r : P →ₗ[ℝ] Module.End ℂ M)
    (a' r' : γ → Module.End ℂ M) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ)
    (har : ∀ X Y, Commute (a X) (r Y)) (ha'r' : ∀ k, Commute (a' k) (r' k))
    (hca : ∀ i j, a (b i) * a (b j) - a (b j) * a (b i) = ∑ k, (c i j k : ℂ) • a' k)
    (hcr : ∀ i j, r (b i) * r (b j) - r (b j) * r (b i) = ∑ k, (c i j k : ℂ) • r' k)
    (hc : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ k (Y : Fin q → P), (a' k + r' k) (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (J : Fin q → β) :
    kDel (r - a) b (kD (a + r) ω) (b ∘ J) +
      ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) =
    ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
      Module.End ℂ M) (ω (b ∘ J)) := by sorry
