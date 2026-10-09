-- Prove2me | Theorems.Thm_StatComplexityDM_E2D_e2d_option_ii_localized_regret
-- name    : StatComplexityDM.E2D.e2d_option_ii_localized_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:52.977361+00:00
-- url     : https://prove2.me/theorems/8697d0ac-5067-4788-9cfb-9f6822581740
-- title:
--   Theorem 4.1 (35), p. 24 / Theorem 4.1a (137), p. 96 — E2D with Option II: Reg_DM ≤ Σ_t sup_{M̄∈co(M)} dec_γ(M_εt(M̄), M̄) + γ·Ẽst_H(T, δ)
-- statement:
--   Let $\Pi$ be a finite set of decisions, rewards lie in $[0,1]$, and let $\mathcal M$ be a class of models (probability kernels) containing the true model $M^\star$. Fix $\delta \in (0,1)$, $\gamma > 0$, $T \in \mathbb N$, and run E2D (Algorithm 1) with Option II and squared confidence radius $R^2 = \widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta)$, with an estimation oracle satisfying Assumption D.1 and producing estimates $\widehat M^{(t)} \in \mathrm{co}(\mathcal M^{(t)})$. Then, with probability at least $1-\delta$,
--   $$
--   \mathrm{Reg}_{\mathrm{DM}} \le \sum_{t=1}^T \sup_{\bar M\in\mathrm{co}(\mathcal M)} \mathrm{dec}_\gamma\big(\mathcal M_{\varepsilon_t}(\bar M), \bar M\big) + \gamma \cdot \widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta),
--   $$
--   where $\mathrm{Reg}_{\mathrm{DM}} = \sum_{t=1}^T \mathbb E_{\pi\sim p^{(t)}}[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi)]$, $\mathcal M_\varepsilon(\bar M) = \{M\in\mathcal M : f^{\bar M}(\pi_{\bar M}) \ge f^M(\pi_M) - \varepsilon\}$ is the localized class, and
--   $$
--   \varepsilon_t := 6\frac{\gamma}{t}\widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta) + \sup_{\bar M\in\mathrm{co}(\mathcal M)} \mathrm{dec}_\gamma(\mathcal M, \bar M) + (2\gamma)^{-1}.
--   $$
--
--   This is the paper's most general upper bound: E2D with Hellinger confidence sets attains regret governed by the *localized* Decision-Estimation Coefficient, the quantity that also appears in the paper's lower bounds.
--
--   **Formalization Note** The statement is pathwise: the run is tied to Algorithm 1 by `IsOptionIIRun` (line 8's arg min relaxed to a certificate, as Remark 4.1 allows), and "with probability at least $1-\delta$" becomes the hypothesis `EventD1`, the event of Assumption D.1. Rounds are 0-based; $\varepsilon_t$ uses the paper's index $t = $ Lean index $+1$. Decisions and outcomes are finite alphabets. The hypothesis $R^2 \ge 1/12$ is added: without it the statement is false (with $R^2 = 0$, $\gamma = 10$, two decisions and two Bernoulli models the first round's regret is positive while the right side is $0$). In applications $\widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta) \ge 2\log(1/\delta)$, so the hypothesis is mild. When a localized class is empty, Lean's convention makes its DEC $0$ rather than $-\infty$, which only weakens the bound.
-- source:
--   arXiv:2112.13487v3, Theorem 4.1, (35), p. 24; Theorem 4.1a, (137), p. 96 (proof pp. 96–99)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_E2D_Run

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- Theorem 4.1, (35), arXiv:2112.13487v3, p. 24, in the form of Theorem 4.1a, (137), p. 96: consider
Algorithm 1 with Option II and `R² = Ẽst_H(T, δ)`, under Assumption D.1, with `R ⊆ [0, 1]` and the
oracle's estimates `M̂^{(t)} ∈ co(M^{(t)})`. Then for any `T` and `γ > 0`, on the event `E` of
Assumption D.1 (probability at least `1 − δ`),
`Reg_DM ≤ Σ_{t=1}^{T} sup_{M̄∈co(M)} dec_γ(M_{ε_t}(M̄), M̄) + γ · Ẽst_H(T, δ)`, where
`ε_t := 6 (γ/t) Ẽst_H(T, δ) + sup_{M̄∈co(M)} dec_γ(M, M̄) + (2γ)^{-1}`.
The statement is pathwise: `hrun` ties `Mhat`, `p`, `Mt` to Algorithm 1, and `hE` is the event.
Rounds are 0-based (`t : Fin T` is the paper's `t + 1`). The hypothesis `1/12 ≤ R2` is not in the
paper; without it the statement fails at the first round (see the mission notes). -/
theorem e2d_option_ii_localized_regret {S Y : Type*} [Fintype S] [Fintype Y] [DecidableEq S]
    (rew : Y → ℝ) (hrew : ∀ y, 0 ≤ rew y ∧ rew y ≤ 1)
    (𝓜 : Set (S → Y → ℝ)) (h𝓜 : ∀ m ∈ 𝓜, StatComplexityDM.LowerBound.IsModel m)
    (piStar : (S → Y → ℝ) → S) (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel rew piStar)
    (Mstar : S → Y → ℝ) (hMstar : Mstar ∈ 𝓜)
    (γ : ℝ) (hγ : 0 < γ) (T : ℕ) (R2 : ℝ) (hR2 : 1 / 12 ≤ R2)
    (Mhat : Fin T → S → Y → ℝ) (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ))
    (hrun : IsOptionIIRun 𝓜 rew piStar γ R2 T Mhat p Mt)
    (hE : EventD1 Mstar Mhat p Mt R2) :
    regret (fM rew Mstar) (piStar Mstar) T p ≤
      ∑ t : Fin T, sSup ((fun mbar : S → Y → ℝ =>
          decGf (localizedSubclass 𝓜 rew piStar mbar
              (epsT γ R2 ((t : ℕ) + 1) (dec 𝓜 rew piStar γ))) rew piStar γ mbar)
          '' convexHull ℝ 𝓜)
        + γ * R2 := by sorry

end StatComplexityDM.E2D
