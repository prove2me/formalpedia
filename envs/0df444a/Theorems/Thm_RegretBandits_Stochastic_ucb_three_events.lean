-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_ucb_three_events
-- name    : RegretBandits.Stochastic.ucb_three_events
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:33:58.963967+00:00
-- url     : https://prove2.me/theorems/b053a74f-4293-413e-ac5e-f72cf5d75c6f
-- title:
--   Eqs. (2.5)–(2.7) — if $(\alpha,\psi)$-UCB plays a suboptimal arm, one of three events holds
-- statement:
--   Run $(\alpha,\psi)$-UCB with $\alpha>0$ on $K\ge2$ arms; let $i^*$ be an optimal arm ($\mu_{i^*}=\mu^*$) and $i$ an arm with gap $\Delta_i>0$ and $\psi^*(\Delta_i/2)>0$. Suppose that at a round $t\le n$ every arm has already been played at least once, and that $I_t=i$. Then at least one of the following holds:
--   $$\hat\mu_{i^*,T_{i^*}(t-1)}+(\psi^*)^{-1}\!\left(\frac{\alpha\ln t}{T_{i^*}(t-1)}\right)\le\mu^*\qquad(2.5)$$
--   $$\hat\mu_{i,T_i(t-1)}>\mu_i+(\psi^*)^{-1}\!\left(\frac{\alpha\ln t}{T_i(t-1)}\right)\qquad(2.6)$$
--   $$T_i(t-1)<\frac{\alpha\ln n}{\psi^*(\Delta_i/2)}.\qquad(2.7)$$
--
--   This deterministic fact about the algorithm reduces the count of pulls of a suboptimal arm to the probabilities of the events (2.5) and (2.6), which the concentration bound (2.3) controls.
--
--   **Formalization Note.** Lean's round $t+1$ is the book's round $t$: counts are taken after round $t$ and the logarithm is $\ln(t+1)$. When $\psi^*(\Delta_i/2)=+\infty$ the right side of (2.7) is read as $0$, as in the book's arithmetic. The hypothesis $\psi^*(\Delta_i/2)>0$ is needed for (2.7) to have its meaning. The hypothesis that every arm has been played is implicit in the book, where the index of an unplayed arm is undefined.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 11, proof of Theorem 2.1, Eqs. (2.5)–(2.7)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB

namespace RegretBandits.Stochastic

open ImprovedLinBandits.UCBDelta

/-- Eqs. (2.5)–(2.7) of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 11): along a run of
(α, ψ)-UCB, if a suboptimal arm `i` is played in round `t + 1 ≤ n` after every arm has been played
at least once, then (with `i*` an optimal arm and `T_j = T_j(t)`) at least one of
(2.5) `μ̂_{i*,T_{i*}} + (ψ*)⁻¹(α ln(t+1)/T_{i*}) ≤ μ*`,
(2.6) `μ̂_{i,T_i} > μ_i + (ψ*)⁻¹(α ln(t+1)/T_i)`,
(2.7) `T_i < α ln n / ψ*(Δ_i/2)` holds. -/
theorem ucb_three_events {Ω : Type*} {K : ℕ} (hK : 2 ≤ K) (ψ : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hrun : IsAlphaPsiUCBRun ψ α X I) (n t : ℕ) (htn : t + 1 ≤ n) (ω : Ω) (i istar : Fin K)
    (hstar : μ istar = bestMean μ) (hgap : 0 < gap μ i)
    (hψpos : (0 : EReal) < legendreFenchel ψ (gap μ i / 2))
    (hplayed : ∀ j, pullCount I j t ω ≠ 0) (hIt : I (t + 1) ω = i) :
    ucbIndex ψ α X I istar t ω ≤ bestMean μ ∨
      μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
        sampleMean X i (pullCount I i t ω) ω ∨
      (pullCount I i t ω : ℝ) <
        α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal := by sorry

end RegretBandits.Stochastic
