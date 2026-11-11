-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_18
-- name    : SwitchingStable.Universal.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:29.061581+00:00
-- url     : https://prove2.me/theorems/254150ee-dcb5-4424-9fdf-5fe5a2740db7
-- title:
--   Lemma 18 — Integer and series certification
-- statement:
--   For the fixed convergent series and exact coefficient formulas of Sections 4–5 and Appendix E,
--   $$2.9689<\Omega<2.969,\quad\chi>\delta_2+2\gamma+2\delta_4+\delta_5+3(\xi+\psi),\quad\chi_{3,2}>\gamma+\delta_4+\delta_5+3\psi.$$
--   All eight $a_i$ and six $B$ coefficients are strictly positive. For every $1\le i\le j\le3$ and $1\le r,t\le3$, all 54 comparisons hold:
--   $$\sum_{a=0}^{r-1}\sum_{b=0}^{t-1}e_{i+j+a+b}\ge\omega_i+\omega_j-p(r)-p(t).$$
--   Moreover $\omega_1>\omega_2>\omega_3$, $\omega_1>0$, $\omega_3<0$, and $\xi,\psi>0$, and the private constant satisfies
--   $$2.114<\exp(C_2)<2.1141.$$
--   The statement also records the convergences, the exact alternate formula for $\Omega$, boundary-cost recurrences, and the unnumbered Appendix E identity $Q-\vartheta N$ equal to its fourteen-term decomposition.
--
--   Differences from the source:
--   - encoding: Infinite series, decimal strict enclosures and the Appendix E coefficient certificate → Shifted natural series with explicit Summable conclusions, exact rational decimal bounds and every coefficient formula; reason: Index shifts change no term; convergence prevents total tsum defaults from certifying junk values; the additional identities are the source proof components, not assumptions.
--   - generalization: The Appendix E identity is applied to occurrence counts of the promoted market → The additional count identity is asserted for every complete strict market; reason: It is an algebraic identity using the defined counts and constants, without the structural count inequalities; specialization to the promoted market is exactly the source identity.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 28, PDF p. 29, Lemma 18; proof-support: Appendix E, The exact count identity (unnumbered), p. 28, PDF p. 29

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_18 :
    (29689/10000 : ℝ) < Omega ∧ Omega < (2969/1000 : ℝ) ∧
    delta 2 + 2*gamma + 2*delta 4 + delta 5 + 3*(xi+psi) < chi ∧
    gamma + delta 4 + delta 5 + 3*psi < chi32 ∧
    (∀ i ∈ Finset.Icc 1 8, 0 < coeffA i) ∧ (∀ i : Fin 6, 0 < coeffB i) ∧
    (∀ i ∈ Finset.Icc 1 3, ∀ j ∈ Finset.Icc i 3,
      ∀ r ∈ Finset.Icc 1 3, ∀ t ∈ Finset.Icc 1 3,
      omega i + omega j - penalty r - penalty t ≤
        ∑ a ∈ Finset.range r, ∑ b ∈ Finset.range t, e (i+j+a+b)) ∧
    omega 2 < omega 1 ∧ omega 3 < omega 2 ∧ 0 < omega 1 ∧ omega 3 < 0 ∧ 0 < xi ∧ 0 < psi ∧
    (2114/1000 : ℝ) < Real.exp C2 ∧ Real.exp C2 < (21141/10000 : ℝ) ∧
    Summable (fun m : ℕ => 2 * Real.log (m+2) / ((m+3)*(m+4))) ∧
    (∀ k ∈ Finset.Icc 1 5, Summable (deltaTerm k) ∧ 0 < delta k) ∧
    Summable (etaTerm 1) ∧ Summable (etaTerm 2) ∧
    Summable (fun m : ℕ => e (m+2)) ∧ Summable chiTerm ∧ Summable privateTerm ∧
    delta 4 = gamma-Real.log (4/3 : ℝ)/60 ∧
    delta 5 = delta 4-Real.log (5/4 : ℝ)/105 ∧
    Omega = Real.exp (C - Real.log 2/18 - 6*delta 2 + 2*Real.log (3/2 : ℝ)/15 +
      Real.log (4/3 : ℝ)/30 + 2*Real.log (5/4 : ℝ)/315 - K) ∧
    (∀ {n : ℕ} (I : StableMatching.Instance n) (ε : Direction),
      let v := occurrenceCounts I ε; v.Q-theta*v.N = v.decomposition) := by sorry

end SwitchingStable.Universal
