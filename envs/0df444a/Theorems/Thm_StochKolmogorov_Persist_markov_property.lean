-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_markov_property
-- name    : StochKolmogorov.Persist.markov_property
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:09:17.431978+00:00
-- url     : https://prove2.me/theorems/b84e17e0-c183-44d5-a567-e69590cf15db
-- title:
--   Markov property and orthant invariance of stochastic Kolmogorov systems
-- statement:
--   Let $X$ be a family of strong solutions of the stochastic Kolmogorov system (1.1), $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i(t)$, one solution $X^x$ from each $x \in \mathbb{R}^n_+$, all driven by one Brownian motion, and suppose Assumption 1.1 holds. Write $P_X(t,x,\cdot)$ for the law of $X^x(t)$. Then
--
--   $$P_X(t,x,\cdot) = \kappa_t(x,\cdot) \text{ on } \mathbb{R}^n_+ \text{ for a Markov kernel } \kappa_t, \qquad P_X(s+t,x,A) = \int P_X(t,y,A)\,P_X(s,x,dy),$$
--
--   and $P_X(t,x,\mathbb{R}^n_+) = 1$ for $x \in \mathbb{R}^n_+$, $P_X(t,x,\mathbb{R}^{n,\circ}_+) = 1$ for $x \in \mathbb{R}^{n,\circ}_+$.
--
--   Role: this is the Markov (Chapman-Kolmogorov) property of the solution together with the invariance of the closed and the open orthant; Theorem 1.1 uses it to pass from the skeleton chain $X(k\tau)$ to all times $t$ (invariance of $\pi^*$ for every $t$, uniqueness, and the rate $C_x r^t$).
--
--   **Formalization Note**: the kernel $\kappa_t$ is only required to agree with $P_X(t,x,\cdot)$ on $\mathbb{R}^n_+$, where the solution family is defined.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, https://arxiv.org/abs/1704.06984, Lemma 3.1 (p. 14, invariance of the faces) and Section 3 (Markov-Feller property of the solution, p. 14); standard Markov property of strong solutions: X. Mao, Stochastic Differential Equations and Applications, Theorem 2.9.3

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem markov_property {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x) ∧
    (∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n), MeasurableSet A →
        trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x)) ∧
    (∀ (t : ℝ≥0) (x : SDEState n), x ∈ orthant n → trans P X t x (orthant n)ᶜ = 0) ∧
    (∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n → trans P X t x (openOrthant n)ᶜ = 0) := by sorry

end StochKolmogorov.Persist
