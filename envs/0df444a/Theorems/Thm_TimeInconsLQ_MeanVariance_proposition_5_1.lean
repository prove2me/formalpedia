-- Prove2me | Theorems.Thm_TimeInconsLQ_MeanVariance_proposition_5_1
-- name    : TimeInconsLQ.MeanVariance.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:30.172195+00:00
-- url     : https://prove2.me/theorems/3cc8244a-1792-446b-abdf-ce9304199824
-- title:
--   Proposition 5.1 — the indefinite stochastic Riccati BSDE (5.8) has a unique bounded solution with M ≥ c > 0, and U · W is BMO
-- statement:
--   Consider the market of §5: a $d$-dimensional Brownian motion $W$, horizon $T>0$, a deterministic bounded measurable interest rate $r$, a progressively measurable essentially bounded risk premium $\theta$, and $\mu_1\ge0$; let $\Gamma^{(1)}_s=\mu_1e^{\int_s^Tr_t\,dt}$. Consider the BSDE
--   $$dM_s=-\big(2r_sM_s-U_s'\theta_s+\Gamma^{(1)}_s|\theta_s|^2-M_s^{-1}|U_s|^2+\Gamma^{(1)}_sM_s^{-1}U_s'\theta_s\big)ds+U_s'\,dW_s,\qquad M_T=1. \tag{5.8}$$
--   Then:
--
--   1. (5.8) has a solution $(M,U)\in L^\infty_{\mathcal F}(0,T;\mathbb R)\times L^2_{\mathcal F}(0,T;\mathbb R^d)$ with $M\ge c$ for some constant $c>0$;
--   2. any two such solutions $(M,U)$, $(M',U')$ coincide: $M_t=M'_t$ a.s. for every $t\in[0,T]$, and $U=U'$ for $ds\otimes dP$-a.e. $(s,\omega)\in[0,T]\times\Omega$;
--   3. for every such solution, $U\cdot W$ is a BMO martingale.
--
--   $M$ is the coefficient of the wealth in the equilibrium adjoint process, and the bounds $c\le M\le C$ are what make the feedback (5.14) well defined.
--
--   **Formalization Note.** "Unique" is read in the natural equivalence classes: $M$ up to modification, $U$ up to $ds\otimes dP$-null sets. "$M\ge c$" holds $ds\otimes dP$-a.e. The BMO property is a conclusion, stated for every solution in the class.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 17, Proposition 5.1, BSDE (5.8)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Market

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Proposition 5.1 (p. 17). The BSDE (5.8) has a solution `(M, U) ∈ L^∞_𝓕(0, T; ℝ) × L²_𝓕(0, T; ℝᵈ)`
with `M ≥ c` for some constant `c > 0`; any two such solutions agree (`M` at every time almost
surely, `U` `ds ⊗ dP`-a.e.); and for every such solution `U · W` is a BMO martingale. -/
theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing) :
    (∃ M U, mk.Class58 M U) ∧
    (∀ M U M' U', mk.Class58 M U → mk.Class58 M' U' →
      (∀ t ≤ mk.T, M t =ᵐ[mk.P] M' t) ∧
      ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) mk.T)).prod mk.P),
        U q.1.toNNReal q.2 = U' q.1.toNNReal q.2) ∧
    (∀ M U, mk.Class58 M U → IsBMO mk.filt mk.P mk.T U) := by sorry

end TimeInconsLQ.MeanVariance
