-- Prove2me | Theorems.Thm_QLearning_Convergence_lemmaB3_arp_model_converges_ae
-- name    : QLearning.Convergence.lemmaB3_arp_model_converges_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:28.288985+00:00
-- url     : https://prove2.me/theorems/33dafa18-152f-4834-8e46-928144da7b55
-- title:
--   Lemma B.3, p. 290 — with probability 1, P^(n)_xy[a] → P_xy[a] and ℛ^(n)_x(a) → ℛ_x(a) as n → ∞
-- statement:
--   Let the real process be a finite controlled Markov process $(X,\mathfrak A,\mathcal R,P)$ and let the episodes $(x_n,a_n,y_n,r_n,\alpha_n)_{n\ge1}$ be generated as in the convergence theorem: on a filtered probability space, $x_n,a_n,\alpha_n$ are $\mathcal F_{n-1}$-measurable, $y_n,r_n$ are $\mathcal F_n$-measurable, $\Pr[y_n=y\mid\mathcal F_{n-1}]=P_{x_ny}[a_n]$, $\mathbb E[r_n\mid\mathcal F_{n-1}]=\mathcal R_{x_n}(a_n)$, $|r_n|\le\mathcal R$, $0\le\alpha_n<1$, and condition (3) holds almost surely for every pair. Let $P^{(n)}_{xy}[a]$ and $\mathcal R^{(n)}_x(a)$ be the aggregated transition probabilities and expected rewards of the action-replay process built from the episodes and initial values $Q_0$. Then with probability $1$, for all $x,a,y$,
--   $$P^{(n)}_{xy}[a]\to P_{xy}[a]\quad\text{and}\quad\mathcal R^{(n)}_x(a)\to\mathcal R_x(a)\qquad\text{as }n\to\infty.$$
--
--   The ARP's one-step model converges to the real one; with Lemma B.4 this makes the ARP's finite-horizon values close to those of the real process.
--
--   **Formalization Note** The probability model is the one pinned for the convergence theorem (the paper describes it only in words). The final paragraph of the paper's proof, about the model conditional on ending above a level $k$, is not part of the lemma's statement and is not included.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), p. 290, Lemma B.3

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace QLearning.Convergence

theorem lemmaB3_arp_model_converges_ae {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (M : FiniteMDP X A) (Q0 : X → A → ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀ n, Measurable[ℱ n] (xs (n + 1)))
    (has : ∀ n, Measurable[ℱ n] (as (n + 1)))
    (hαs : ∀ n, Measurable[ℱ n] (αs (n + 1)))
    (hys : ∀ n, Measurable[ℱ (n + 1)] (ys (n + 1)))
    (hrs : ∀ n, Measurable[ℱ (n + 1)] (rs (n + 1)))
    (htrans : ∀ n y, μ[fun ω => if ys (n + 1) ω = y then (1 : ℝ) else 0 | ℱ n]
      =ᵐ[μ] fun ω => M.P (xs (n + 1) ω) (as (n + 1) ω) y)
    (hrew : ∀ n, μ[rs (n + 1) | ℱ n] =ᵐ[μ] fun ω => M.R (xs (n + 1) ω) (as (n + 1) ω))
    (Rbar : ℝ) (hbdd : ∀ n ω, |rs n ω| ≤ Rbar)
    (hα : ∀ n ω, 0 ≤ αs n ω ∧ αs n ω < 1)
    (h3 : ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1)) atTop atTop ∧
      Summable (fun n =>
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ x a,
      (∀ y, Tendsto (fun n => arpTrans (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
          (fun k => αs k ω) n x a y) atTop (𝓝 (M.P x a y))) ∧
      Tendsto (fun n => arpReward (fun k => xs k ω) (fun k => as k ω) (fun k => rs k ω)
          (fun k => αs k ω) Q0 n x a) atTop (𝓝 (M.R x a)) := by sorry

end QLearning.Convergence
