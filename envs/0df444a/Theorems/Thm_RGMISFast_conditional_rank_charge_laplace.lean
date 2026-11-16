-- Prove2me | Theorems.Thm_RGMISFast_conditional_rank_charge_laplace
-- name    : RGMISFast.conditional_rank_charge_laplace
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T23:12:26.841972+00:00
-- url     : https://prove2.me/theorems/d0249003-db5d-4721-90bd-2852abb9c4f2
-- title:
--   Memoryless product integral of the capped seed rank charges
-- statement:
--   Let $\mu$ be the explicit exponential conditional rank law at time $\theta$, let $a>0$ with $\theta<a$, and let $A$ be any finite set. For every real $L$, with $E=\{r(v)\ge a\text{ for all }v\in A\}$,
--   $$\int_E e^{-(2S(A,a)+L)}\,d\mu=\mu(E)e^{-L}\gamma(a)^{|A|}.$$
--   This isolates the memorylessness and independence calculation in the proof of Equation (29). If a vertex in $A$ is already revealed, its rank is below $\theta<a$, so both sides vanish. Otherwise, conditional on $E$, the coordinates in $A$ are independent $a+\mathrm{Exp}(1)$ variables. Factor the exponential of the rank sum and integrate the finite product to obtain $\gamma(a)^{|A|}$. The empty-set case is included. This auxiliary statement generalizes the paper's choice $\theta=a/2$ and $a=a_m$; it has no graph or activity assumptions because it is purely a product-measure identity.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §6.2, proof of Lemma 3.1, paragraph preceding Equation (29), printed p.25 (PDF p.27), manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664.

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_gammaA
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.conditional_rank_charge_laplace {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ a L : ℝ) (ha : 0 < a) (hθa : θ < a) (A : Finset V) :
    (∫⁻ r in {r | ∀ v ∈ A, a ≤ r v},
      ENNReal.ofReal (Real.exp (-(2 * S r A a + L))) ∂(condLaw r₀ θ ∅ (fun _ => 0))) =
      condLaw r₀ θ ∅ (fun _ => 0) {r | ∀ v ∈ A, a ≤ r v} *
        ENNReal.ofReal (Real.exp (-L) * gammaA a ^ A.card) := by sorry
