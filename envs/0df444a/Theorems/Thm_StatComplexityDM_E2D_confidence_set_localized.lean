-- Prove2me | Theorems.Thm_StatComplexityDM_E2D_confidence_set_localized
-- name    : StatComplexityDM.E2D.confidence_set_localized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:34.013965+00:00
-- url     : https://prove2.me/theorems/9eee1728-80c3-4428-a337-26489bba46e7
-- title:
--   App. D.1, pp. 98–99 — the confidence sets are localized: M^(t) ⊆ M_εt(M̂^(t)) (for R² ≥ 1/12)
-- statement:
--   Assume rewards lie in $[0,1]$ and consider a run of E2D with Option II, exploration parameter $\gamma > 0$ and squared confidence radius $R^2 \ge 1/12$. For a reference model $\bar M$ and $\varepsilon \ge 0$ let
--   $$
--   \mathcal M_\varepsilon(\bar M) = \{ M \in \mathcal M : f^{\bar M}(\pi_{\bar M}) \ge f^M(\pi_M) - \varepsilon \}
--   $$
--   be the localized class (9). Then for every round $t = 1,\dots,T$,
--   $$
--   \mathcal M^{(t)} \subseteq \mathcal M_{\varepsilon_t}(\widehat M^{(t)}), \qquad \varepsilon_t = 6\frac{\gamma}{t} R^2 + 2\sup_{\bar M\in\mathrm{co}(\mathcal M)} \mathrm{dec}_\gamma(\mathcal M, \bar M) + (2\gamma)^{-1}.
--   $$
--
--   This containment is the step that turns the regret bound of E2D with Option II into a bound in terms of the localized Decision-Estimation Coefficient.
--
--   **Formalization Note** Rounds are 0-based, so the radius is evaluated at `(t : ℕ) + 1`. The hypothesis $R^2 \ge 1/12$ is not in the paper: at the first round $\mathcal M^{(1)} = \mathcal M$, and the containment needs $\varepsilon_1 \ge 1$, which $(2\gamma)^{-1} + 6\gamma R^2 \ge 2\sqrt{3R^2}$ guarantees exactly when $R^2 \ge 1/12$; with $R^2 = 0$ and a single decision, two models with mean rewards $0$ and $1$ violate it for $\gamma > 1/2$. This milestone uses the p. 99 proof radius with $2\cdot\sup\mathrm{dec}$; the printed theorem (35) uses $1\cdot\sup\mathrm{dec}$. The containment is deterministic and needs no event.
-- source:
--   arXiv:2112.13487v3, App. D.1, proof of Theorem 4.1a, pp. 98–99 ("It follows that M^(t) ⊆ M_εt(M̂^(t))")

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_E2D_Run

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- Containment of the confidence sets in localized classes (App. D.1, proof of Theorem 4.1a,
arXiv:2112.13487v3, pp. 98–99): assume `R ⊆ [0, 1]` and consider a run of E2D with Option II, with
`R² ≥ 1/12`. Then for every round `t`, `M^{(t)} ⊆ M_{ε_t}(M̂^{(t)})`, where
`M_ε(M̄) = {M ∈ M : f^{M̄}(π_{M̄}) ≥ f^M(π_M) − ε}` is the localized class (9) and
`ε_t = 6 (γ/t) R² + 2 sup_{M̄∈co(M)} dec_γ(M, M̄) + (2γ)^{-1}` is the radius derived on p. 99. Rounds are
0-based: the Lean round `t : Fin T` is the paper's round `t + 1`, so the radius is evaluated at
`(t : ℕ) + 1`. The hypothesis `1/12 ≤ R2` is needed at the first round, where `M^{(1)} = M`. -/
theorem confidence_set_localized {S Y : Type*} [Fintype S] [Fintype Y]
    (rew : Y → ℝ) (hrew : ∀ y, 0 ≤ rew y ∧ rew y ≤ 1)
    (𝓜 : Set (S → Y → ℝ)) (h𝓜 : ∀ m ∈ 𝓜, StatComplexityDM.LowerBound.IsModel m)
    (piStar : (S → Y → ℝ) → S) (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel rew piStar)
    (γ : ℝ) (hγ : 0 < γ) (T : ℕ) (R2 : ℝ) (hR2 : 1 / 12 ≤ R2)
    (Mhat : Fin T → S → Y → ℝ) (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ))
    (hrun : IsOptionIIRun 𝓜 rew piStar γ R2 T Mhat p Mt) :
    ∀ t : Fin T, Mt t ⊆
      localizedSubclass 𝓜 rew piStar (Mhat t) (epsT γ R2 ((t : ℕ) + 1) (2 * dec 𝓜 rew piStar γ)) := by sorry

end StatComplexityDM.E2D
