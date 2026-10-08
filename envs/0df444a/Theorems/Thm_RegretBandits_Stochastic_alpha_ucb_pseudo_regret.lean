-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_alpha_ucb_pseudo_regret
-- name    : RegretBandits.Stochastic.alpha_ucb_pseudo_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:34:24.441988+00:00
-- url     : https://prove2.me/theorems/b797d63e-e173-4514-8eb9-10e3b689531a
-- title:
--   Eq. (2.4) — pseudo-regret of $\alpha$-UCB for $[0,1]$ rewards
-- statement:
--   Consider a stochastic bandit with $K\ge2$ arms whose rewards take values in $[0,1]$, with means $\mu_i$, $\mu^*=\max_i\mu_i$ and gaps $\Delta_i=\mu^*-\mu_i$. Taking $\psi(\lambda)=\lambda^2/8$ in (2.2) (Hoeffding's lemma) gives $\psi^*(\varepsilon)=2\varepsilon^2$, and $(\alpha,\psi)$-UCB with this $\psi$ is called $\alpha$-UCB. For $\alpha>2$ and every horizon $n$,
--   $$\overline R_n\le\sum_{i:\Delta_i>0}\left(\frac{2\alpha}{\Delta_i}\ln n+\frac{\alpha}{\alpha-2}\right).$$
--
--   This is the most used special case of Theorem 2.1, for bounded rewards; the matching lower bound in its dependence on $\ln n/\Delta_i$ is Theorem 2.2 combined with (2.8).
--
--   **Formalization Note.** The algorithm is run with $\psi(\lambda)=\lambda^2/8$ and plays every arm once before using the index. Rewards lie in $[0,1]$ almost surely. Here $\Delta_i\le1$, so the printed constant $\alpha/(\alpha-2)$ is correct as stated.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 11, Eq. (2.4)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB

namespace RegretBandits.Stochastic

open MeasureTheory ImprovedLinBandits.UCBDelta

/-- Eq. (2.4) of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 11): for `[0, 1]`-valued rewards,
α-UCB, i.e. (α, ψ)-UCB with `ψ(λ) = λ²/8` (Hoeffding's lemma, `ψ*(ε) = 2ε²`) and `α > 2`, satisfies
`R̄_n ≤ ∑_{i : Δ_i > 0} ((2α/Δ_i) ln n + α/(α - 2))`. -/
theorem alpha_ucb_pseudo_regret {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun (fun l => l ^ 2 / 8) α X I) (n : ℕ) :
    pseudoRegretBar P μ I n ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        (2 * α / gap μ i * Real.log (n : ℝ) + α / (α - 2)) := by sorry

end RegretBandits.Stochastic
