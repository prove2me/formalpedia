-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_theorem_1_1
-- name    : PolymerEndpoint.Atomic.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:00.321991+00:00
-- url     : https://prove2.me/theorems/c9efcabf-0cb3-421d-acff-6730f49dedb9
-- title:
--   Theorem 1.1 — asymptotic pure atomicity exactly at low temperature
-- statement:
--   Fix a dimension $d\geq1$ and an inverse temperature $\beta\geq0$. Let $(X_{i,x})_{i\geq1,\,x\in\mathbb Z^d}$ be i.i.d. real random variables with a common law $\mathfrak L$ that is not a point mass and satisfies
--   $$
--   \lambda(\alpha)=\log\mathbb E\,e^{\alpha X_{1,0}}<\infty\qquad\text{for all }\alpha\in[-2\beta,2\beta].
--   $$
--   For $n\geq0$ the quenched polymer measure $\rho_n$ weights each nearest-neighbour path $\gamma$ of length $n$ from the origin proportionally to $\exp(\beta\sum_{i=1}^nX_{i,\gamma(i)})$; $Z_n$ is the partition function (with the factor $(2d)^{-n}$) and $F_n=\frac1n\log Z_n$. Let $f_i(x)=\rho_i(\omega_i=x)$ be the endpoint probability mass function and, for $\varepsilon>0$, let $\mathcal A_i^\varepsilon=\{x\in\mathbb Z^d:f_i(x)>\varepsilon\}$ be the set of $\varepsilon$-atoms, so that $\rho_i(\omega_i\in\mathcal A_i^\varepsilon)=\sum_{x:f_i(x)>\varepsilon}f_i(x)$. The critical inverse temperature $\beta_c$ is characterized by Theorem A: $\lim_n\mathbb E F_n=\lambda(\beta)$ when $0\leq\beta\leq\beta_c$ and $\lim_n\mathbb E F_n<\lambda(\beta)$ when $\beta>\beta_c$.
--
--   1. If $\beta>\beta_c$, then for every sequence $(\varepsilon_i)_{i\geq0}$ of positive numbers tending to $0$,
--   $$
--   \lim_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\rho_i(\omega_i\in\mathcal A_i^{\varepsilon_i})=1\quad\text{almost surely}.
--   $$
--   2. If $0\leq\beta\leq\beta_c$, then there exists a sequence $(\varepsilon_i)_{i\geq0}$ of positive numbers tending to $0$ such that
--   $$
--   \lim_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\rho_i(\omega_i\in\mathcal A_i^{\varepsilon_i})=0\quad\text{almost surely}.
--   $$
--
--   The endpoint distribution is asymptotically purely atomic exactly in the low-temperature phase: there, in Cesàro mean, all of its mass sits on atoms of size bounded below by any vanishing threshold, while at high temperature a suitable vanishing threshold captures none of it.
--
--   **Formalization Note** "$\beta>\beta_c$" is encoded as: $\mathbb E F_n$, computed on the canonical product environment with law $\mathfrak L$, converges to a limit strictly below $\lambda(\beta)$; "$0\leq\beta\leq\beta_c$" as: it converges to $\lambda(\beta)$ (Theorem A, p. 5; the limit exists by (1.5)). The environment is indexed by $\mathbb N\times\mathbb Z^d$; the row $i=0$ is never read. The sequence in clause 2 is chosen before the almost-sure event, so it does not depend on the realization of the environment.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 16, Theorem 1.1; p. 43, Theorem 6.3

import Definitions.Def_PolymerEndpoint_Atomic_Functionals

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem theorem_1_1 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 ≤ β) (hmom : MomentCondition 𝔏 β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Cell d → Ω → ℝ)
    (henv : IsEnvironment X 𝔏 P) :
    (LowTemp (d := d) 𝔏 β → AsympPurelyAtomic X β P) ∧
    (HighTemp (d := d) 𝔏 β →
      ∃ ε : ℕ → ℝ, (∀ i, 0 < ε i) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᵐ a ∂P, Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, atomMass X β i (ε i) a) atTop (𝓝 0)) := by sorry

end PolymerEndpoint.Atomic
