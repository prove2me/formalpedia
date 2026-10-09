-- Prove2me | Theorems.Thm_StatComplexityDM_E2D_confidence_sets_contain_truth
-- name    : StatComplexityDM.E2D.confidence_sets_contain_truth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:41.635404+00:00
-- url     : https://prove2.me/theorems/0cb9d276-9bfa-4bd9-8a01-df3d55e7cf16
-- title:
--   Lemma D.1, p. 97 — under E, M⋆ ∈ M^(t) for all t ≤ T and Est_H ≤ Ẽst_H(T, δ)
-- statement:
--   Consider a run of E2D with Option II and confidence radius $R^2 = \widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta)$ (Algorithm 1), for a model class $\mathcal M$ containing the true model $M^\star$, and suppose the event $\mathcal E$ of Assumption D.1 holds on the run. Then $M^\star \in \mathcal M^{(t)}$ for all $t \le T$, and consequently
--   $$
--   \mathrm{Est}_{\mathrm H} = \sum_{t=1}^T \mathbb E_{\pi^{(t)}\sim p^{(t)}}\big[D^2_{\mathrm H}(M^\star(\pi^{(t)}), \widehat M^{(t)}(\pi^{(t)}))\big] \le \widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta).
--   $$
--
--   The lemma says that the Hellinger confidence sets never discard the true model on the good event, so the minimax problems of Option II are always solved over a class containing $M^\star$.
--
--   **Formalization Note** The statement is pathwise: the run is tied to Algorithm 1 by `IsOptionIIRun`, and the event is the hypothesis `EventD1`, which holds with probability at least $1-\delta$ under Assumption D.1. Rounds are 0-based. Decisions and outcomes are finite alphabets.
-- source:
--   arXiv:2112.13487v3, App. D.1, Lemma D.1, p. 97

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_E2D_Run

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- Lemma D.1, arXiv:2112.13487v3, p. 97: on the event `E` of Assumption D.1, along a run of E2D
with Option II and `R² = Ẽst_H(T, δ)`, the confidence sets contain the true model,
`M⋆ ∈ M^{(t)}` for all `t ≤ T`, and consequently
`Est_H = Σ_t E_{π∼p^{(t)}}[D²_H(M⋆(π), M̂^{(t)}(π))] ≤ Ẽst_H(T, δ)`. Rounds are 0-based. -/
theorem confidence_sets_contain_truth {S Y : Type*} [Fintype S] [Fintype Y]
    (rew : Y → ℝ) (𝓜 : Set (S → Y → ℝ)) (piStar : (S → Y → ℝ) → S)
    (Mstar : S → Y → ℝ) (hMstar : Mstar ∈ 𝓜) (γ : ℝ) (T : ℕ) (R2 : ℝ)
    (Mhat : Fin T → S → Y → ℝ) (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ))
    (hrun : IsOptionIIRun 𝓜 rew piStar γ R2 T Mhat p Mt)
    (hE : EventD1 Mstar Mhat p Mt R2) :
    (∀ t : Fin T, Mstar ∈ Mt t) ∧
      ∑ t : Fin T, ∑ π, p t π * hellingerSq (Mstar π) (Mhat t π) ≤ R2 := by sorry

end StatComplexityDM.E2D
