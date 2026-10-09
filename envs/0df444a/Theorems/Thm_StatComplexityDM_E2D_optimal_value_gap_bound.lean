-- Prove2me | Theorems.Thm_StatComplexityDM_E2D_optimal_value_gap_bound
-- name    : StatComplexityDM.E2D.optimal_value_gap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:41.993992+00:00
-- url     : https://prove2.me/theorems/daf52ef2-56b4-4a71-b094-b4928860df20
-- title:
--   Lemma D.2, (139), p. 97 — f^M(π_M) − f^{M̄}(π_{M̄}) ≤ (2γ)⁻¹ + (1/t)Σ_{i≤t}(dec_γ(M^(i), M̂^(i)) + 2γ·E D²_H(M, M̂^(i)) + γ·E D²_H(M̄, M̂^(i)))
-- statement:
--   Assume rewards lie in $[0,1]$ and consider a run of E2D with Option II and exploration parameter $\gamma > 0$. Let $M$ be a model with $M \in \mathcal M^{(i)}$ for all $i \le t$. Then for any model $\bar M$ (not necessarily in $\mathcal M$),
--   $$
--   f^M(\pi_M) - f^{\bar M}(\pi_{\bar M}) \le (2\gamma)^{-1} + \frac1t \sum_{i=1}^t \Big( \mathrm{dec}_\gamma(\mathcal M^{(i)}, \widehat M^{(i)}) + 2\gamma\, \mathbb E_{\pi\sim p^{(i)}}\big[D^2_{\mathrm H}(M(\pi), \widehat M^{(i)}(\pi))\big] + \gamma\, \mathbb E_{\pi\sim p^{(i)}}\big[D^2_{\mathrm H}(\bar M(\pi), \widehat M^{(i)}(\pi))\big] \Big).
--   $$
--
--   This is the key technical lemma of the localized analysis: it converts the confidence-set membership of $M$ and the closeness of $\bar M$ to the estimates into a bound on how much larger the optimal value of $M$ can be than that of $\bar M$, which is what places the confidence sets inside localized classes.
--
--   **Formalization Note** Rounds are 0-based: the Lean round `t : Fin T` is the paper's round $t+1$, so the average runs over the $t+1$ Lean rounds $i \le t$ with weight $1/(t+1)$. The model $\bar M$ is any probability kernel. The run is tied to Algorithm 1 by `IsOptionIIRun`; Lemma D.2 is deterministic and needs no event. Decisions and outcomes are finite alphabets.
-- source:
--   arXiv:2112.13487v3, App. D.1, Lemma D.2, (139), p. 97

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_E2D_Run

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- Lemma D.2, (139), arXiv:2112.13487v3, p. 97: assume `R ⊆ [0, 1]`, and consider a run of E2D
with Option II. Let `M` be a model with `M ∈ M^{(i)}` for all `i ≤ t`. Then for any model `M̄`
(not necessarily in `M`),
`f^M(π_M) − f^{M̄}(π_{M̄}) ≤ (2γ)^{-1} + (1/t) Σ_{i=1}^{t} (dec_γ(M^{(i)}, M̂^{(i)})
  + 2γ E_{π∼p^{(i)}}[D²_H(M(π), M̂^{(i)}(π))] + γ E_{π∼p^{(i)}}[D²_H(M̄(π), M̂^{(i)}(π))])`.
Rounds are 0-based: the Lean round `t : Fin T` is the paper's round `t + 1`, so the average runs
over the `t + 1` Lean rounds `i ≤ t`. -/
theorem optimal_value_gap_bound {S Y : Type*} [Fintype S] [Fintype Y]
    (rew : Y → ℝ) (hrew : ∀ y, 0 ≤ rew y ∧ rew y ≤ 1)
    (𝓜 : Set (S → Y → ℝ)) (h𝓜 : ∀ m ∈ 𝓜, StatComplexityDM.LowerBound.IsModel m)
    (piStar : (S → Y → ℝ) → S) (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel rew piStar)
    (γ : ℝ) (hγ : 0 < γ) (T : ℕ) (R2 : ℝ)
    (Mhat : Fin T → S → Y → ℝ) (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ))
    (hrun : IsOptionIIRun 𝓜 rew piStar γ R2 T Mhat p Mt)
    (t : Fin T) (m : S → Y → ℝ) (hm : ∀ i : Fin T, i ≤ t → m ∈ Mt i)
    (mbar : S → Y → ℝ) (hmbar : StatComplexityDM.LowerBound.IsModel mbar) :
    fM rew m (piStar m) - fM rew mbar (piStar mbar) ≤
      (2 * γ)⁻¹ + (1 / ((t : ℕ) + 1 : ℝ)) * ∑ i : Fin T with i ≤ t,
        (decGf (Mt i) rew piStar γ (Mhat i)
          + 2 * γ * ∑ π, p i π * hellingerSq (m π) (Mhat i π)
          + γ * ∑ π, p i π * hellingerSq (mbar π) (Mhat i π)) := by sorry

end StatComplexityDM.E2D
