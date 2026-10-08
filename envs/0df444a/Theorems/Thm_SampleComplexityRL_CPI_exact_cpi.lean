-- Prove2me | Theorems.Thm_SampleComplexityRL_CPI_exact_cpi
-- name    : SampleComplexityRL.CPI.exact_cpi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:08.212181+00:00
-- url     : https://prove2.me/theorems/f16a915e-8feb-4cbf-9208-264ad6824ea0
-- title:
--   Theorem 7.3.2 (Exact CPI, explicit-constant form) — strict improvement per update, halting within 8H²/ε² updates, future advantages ≤ ε/H
-- statement:
--   Consider a finite MDP with nonempty state set $S$, nonempty action set $A$, transition kernel $P$, rewards $r(s,a)\in[0,1]$ and discount $0\le\gamma<1$, with normalized values. Let $H=1/(1-\gamma)$, let $\mu$ be a reset distribution on $S$, let $\varepsilon>0$, and let $\Pi$ be a nonempty class of stationary policies. Write $V_\pi(\mu)=\mathbb E_{s\sim\mu}[V_\pi(s)]$, $\mathbb Q_\pi(\mu,h)$ for the future state-action value and $\mathbb A_\pi(\mu,h)=\mathbb E_{s\sim d_{\pi,\mu}}\mathbb E_{a\sim h(\cdot\mid s)}[A_\pi(s,a)]$ for the future advantage.
--
--   Run **Exact CPI** (Algorithm 11): from a stationary policy $\pi_0$, at each round $k$ the ExactPolicyChooser returns $\pi'_k\in\arg\max_{h\in\Pi}\mathbb Q_{\pi_k}(\mu,h)$; if $\mathbb A_{\pi_k}(\mu,\pi'_k)>\varepsilon/H$, the algorithm sets $\alpha_k=\mathbb A_{\pi_k}(\mu,\pi'_k)/(4H)$ and $\pi_{k+1}=(1-\alpha_k)\pi_k+\alpha_k\pi'_k$; otherwise it halts and returns $\pi_k$. Then there is a halting round $K$ such that
--
--   1. the number of updates is bounded:
--   $$K<\frac{8H^2}{\varepsilon^2},$$
--   so the ExactPolicyChooser is called $K+1$ times;
--   2. every update strictly improves the value: for every $k<K$ the test passes and
--   $$V_{\pi_{k+1}}(\mu)-V_{\pi_k}(\mu)>\frac{\varepsilon^2}{8H^2};$$
--   3. at round $K$ the test fails, $\mathbb A_{\pi_K}(\mu,\pi'_K)\le\varepsilon/H$, so the algorithm halts and returns $\pi_K$;
--   4. the returned $\pi_K$ is a stationary policy and, for all $h\in\Pi$,
--   $$\mathbb A_{\pi_K}(\mu,h)\le\frac{\varepsilon}{H}.$$
--
--   This is the guarantee of the exact version of conservative policy iteration: a monotone sequence of policies that stops after polynomially many updates in the horizon and the accuracy, with an output that no policy of the class can improve much in the future-advantage sense. The output is in general not a member of $\Pi$.
--
--   **Formalization Note** This is the **explicit-constant form** of Theorem 7.3.2: the thesis states "halts after $O(H^2/\varepsilon^2)$ calls" and "improves the value after each update"; the constant $8$ is the one Corollary 7.2.3 gives (improvement at least $\mathbb A^2/8>(\varepsilon/H)^2/8$ per update, with values in $[0,1]$). The ExactPolicyChooser is encoded by its argmax property over $\Pi$, which is an assumption on the run; the halting round is part of the conclusion, not an assumption. In Lean the class is named `Pi`.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 90, Theorem 7.3.2 (Exact CPI), with Algorithm 11 (p. 90) and Corollary 7.2.3 (p. 87)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_CPI_ExactCPI
open ApproxOptRL.Shared ApproxOptRL.CPI FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.CPI

/-- **Theorem 7.3.2 (Exact CPI)**, Kakade 2003, p. 90, in **explicit-constant form**: the
thesis's `O(H²/ε²)` is pinned to the constant `8` that Corollary 7.2.3 gives (improvement
`≥ 𝔸²/8 > ε²/(8H²)` per update, values in `[0, 1]`).
For every run `(π, π')` of Exact CPI (Algorithm 11) with policy class `Pi`, reset distribution `μ`
and accuracy `ε > 0`, there is a halting round `K` such that
1. `K < 8H²/ε²` (so the ExactPolicyChooser is called `K + 1` times);
2. at every round `k < K` the test `𝔸_{π k}(μ, π' k) > ε/H` passes and the update strictly
   improves `V_π(μ)`, by more than `ε²/(8H²)`;
3. at round `K` the test fails, so the algorithm halts and returns `π K`;
4. `π K` is a stationary policy with `𝔸_{π K}(μ, h) ≤ ε/H` for every `h ∈ Pi`.
`H = 1/(1 − γ)`; values are normalized. -/
theorem exact_cpi {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (ε : ℝ) (hε : 0 < ε)
    (Pi : Set (S → A → ℝ)) (hPi_ne : Pi.Nonempty) (hPi : ∀ h ∈ Pi, IsPolicy h)
    (π π' : ℕ → S → A → ℝ) (hrun : IsExactCPIRun P r γ μ ε Pi π π') :
    ∃ K : ℕ,
      (K : ℝ) < 8 * horizon γ ^ 2 / ε ^ 2 ∧
      (∀ k < K, ε / horizon γ < policyAdvantage P r γ (π k) μ (π' k) ∧
        ε ^ 2 / (8 * horizon γ ^ 2) < eta P r γ (π (k + 1)) μ - eta P r γ (π k) μ) ∧
      policyAdvantage P r γ (π K) μ (π' K) ≤ ε / horizon γ ∧
      IsPolicy (π K) ∧
      ∀ h ∈ Pi, policyAdvantage P r γ (π K) μ h ≤ ε / horizon γ := by sorry

end SampleComplexityRL.CPI
