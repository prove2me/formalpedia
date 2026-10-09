-- Prove2me | Theorems.Thm_StatComplexityDM_E2D_e2d_round_bound
-- name    : StatComplexityDM.E2D.e2d_round_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:03.928991+00:00
-- url     : https://prove2.me/theorems/9a62701a-eb83-4055-bb45-93d71e4a1117
-- title:
--   (138), p. 97 — one E2D round: E_p[f^{M⋆}(π_{M⋆}) − f^{M⋆}(π)] − γ·E_p[D²_H(M⋆(π), M̂(π))] ≤ dec_γ(M, M̂)
-- statement:
--   Let $\mathcal C$ be a class of models on finite decision and outcome sets, with rewards in $[0,1]$, containing the true model $M^\star$. Let $\widehat M$ be a reference model, $\gamma > 0$, and let $p \in \Delta(\Pi)$ be a minimizer of the E2D minimax problem, i.e.
--   $$
--   \sup_{M\in\mathcal C} \mathbb E_{\pi\sim p}\big[f^M(\pi_M) - f^M(\pi) - \gamma\, D^2_{\mathrm H}(M(\pi), \widehat M(\pi))\big] = \mathrm{dec}_\gamma(\mathcal C, \widehat M).
--   $$
--   Then
--   $$
--   \mathbb E_{\pi\sim p}\big[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi)\big] - \gamma\, \mathbb E_{\pi\sim p}\big[D^2_{\mathrm H}(M^\star(\pi), \widehat M(\pi))\big] \le \mathrm{dec}_\gamma(\mathcal C, \widehat M).
--   $$
--
--   This is the per-round step of every E2D regret bound: the instantaneous regret, offset by the Hellinger estimation error, is at most the Decision-Estimation Coefficient. The paper states it for $\mathcal C = \mathcal M$ (Option I) and reuses it for the confidence sets $\mathcal C = \mathcal M^{(t)}$ (Option II, p. 98).
--
--   **Formalization Note** Decisions and outcomes are finite alphabets. The class $\mathcal C$ is a parameter so the step covers both options. The minimizing property is stated as an equality between the supremum at $p$ and `decGf`; the boundedness that makes the supremum meaningful comes from the hypotheses that every member of $\mathcal C$ is a probability kernel and that rewards lie in $[0,1]$.
-- source:
--   arXiv:2112.13487v3, App. D.1, proof of Theorem 4.1, (138), p. 97

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- (138), arXiv:2112.13487v3, p. 97: the per-round step of E2D. Let `C` be the model class over
which the round's minimax problem is solved (the class `M` for Option I, the confidence set
`M^{(t)}` for Option II), containing the true model `M⋆`, with every member a probability kernel
and rewards in `[0, 1]`. If `p` is a distribution on `Π` minimizing
`sup_{M∈C} V^{M̂}_γ(p, M)` (line 5 / line 8 of Algorithm 1), so that this supremum equals
`dec_γ(C, M̂)`, then
`E_{π∼p}[f^{M⋆}(π_{M⋆}) − f^{M⋆}(π)] − γ · E_{π∼p}[D²_H(M⋆(π), M̂(π))] ≤ dec_γ(C, M̂)`. -/
theorem e2d_round_bound {S Y : Type*} [Fintype S] [Fintype Y]
    (rew : Y → ℝ) (hrew : ∀ y, 0 ≤ rew y ∧ rew y ≤ 1)
    (piStar : (S → Y → ℝ) → S) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (S → Y → ℝ)) (hC : ∀ m ∈ C, StatComplexityDM.LowerBound.IsModel m)
    (Mstar : S → Y → ℝ) (hMstar : Mstar ∈ C) (mhat : S → Y → ℝ)
    (p : S → ℝ) (hp : StatComplexityDM.LowerBound.IsDist p)
    (hpmin : sSup ((fun m : S → Y → ℝ =>
        ∑ π, p π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat π))) '' C)
      = decGf C rew piStar γ mhat) :
    ∑ π, p π * (fM rew Mstar (piStar Mstar) - fM rew Mstar π)
        - γ * ∑ π, p π * hellingerSq (Mstar π) (mhat π)
      ≤ decGf C rew piStar γ mhat := by sorry

end StatComplexityDM.E2D
