-- Prove2me | Theorems.Thm_RGMISFast_root_count_arrival_expansion
-- name    : RGMISFast.root_count_arrival_expansion
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-16T01:07:26.248205+00:00
-- url     : https://prove2.me/theorems/ba6bffdb-a8e4-4232-82aa-29965ff2cd37
-- title:
--   Finite exponential expansions for the root count and destruction rate
-- statement:
--   Fix $k\ge1$, a time horizon $t>0$, and a prescribed root rank $\rho\ge t$. There are a finite degree $n$ and real coefficients $c_j$ such that, for every $s\in[0,t]$,
--   $$\mathbb E[Y_k(s)\mid r(u)=\rho]=\sum_{j=0}^n c_j e^{-js},$$
--   $$\mathbb E[\sum_W d_s(W)\mid r(u)=\rho]=\sum_{j=0}^n j c_j e^{-js}.$$
--   The coefficients are not required to be nonnegative. Both expectations use the explicit product law with fixed root rank and independent exponential non-root ranks.
--
--   This algebraic auxiliary formulation isolates the finite-arrival-order calculation in the proof of Equation (20). The paper observes that the expected count is a polynomial in $e^{-s}$, obtained by summing over arrival sets and their relative orders. The paired coefficient identity expresses the destruction-rate calculation for that same finite process. Unlike the target, this auxiliary statement contains no derivative or limiting assertion: termwise differentiation of the finite expansion is proved separately. The closed interval is appropriate because ranks equal to the checkpoint remain active there.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §5.1, proof of Lemma 5.2, printed pp.18–19 (PDF pp.20–21), polynomial-in-exp(-s) observation and the short-window destruction calculation yielding Equation (20). Auxiliary finite exponential-basis reformulation.

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.root_count_arrival_expansion {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (hk : 1 ≤ k)
    (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    ∃ (n : ℕ) (coeff : ℕ → ℝ),
      (∀ s ∈ Set.Icc 0 t,
        (∫ r, (Y G u k s r : ℝ) ∂(rootLaw u ρ)) =
          ∑ j ∈ Finset.range (n+1), coeff j * Real.exp (-(j:ℝ)*s)) ∧
      (∀ s ∈ Set.Icc 0 t,
        (∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ)) =
          ∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j * Real.exp (-(j:ℝ)*s)) := by sorry
