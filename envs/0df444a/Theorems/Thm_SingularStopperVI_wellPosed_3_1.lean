-- Prove2me | Theorems.Thm_SingularStopperVI_wellPosed_3_1
-- name    : SingularStopperVI.wellPosed_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:44.40962+00:00
-- url     : https://prove2.me/theorems/258cfddb-24a6-4cf5-980e-21b0d96cbb73
-- title:
--   Well-posedness of the controlled equation (3.1)
-- statement:
--   Let $b,\sigma$ satisfy Assumption 3.1. For $t\in[0,T]$, $x\in\mathbb R^d$ and an admissible pair $(n,\nu)\in\mathcal A_t$, the controlled equation
--
--   $$
--   X_s=x+\int_0^s b(X_u)\,du+\int_0^s\sigma(X_u)\,dW_u+\int_{[0,s]}n_u\,d\nu_u,\qquad 0\le s\le T-t,
--   $$
--
--   with $X$ adapted and càdlàg, has a solution, and any two solutions are indistinguishable on $[0,T-t]$.
--
--   This shows that the infima of the game over pairs $(n,\nu)$ and over triples $(n,\nu,X)$ agree.
--
--   Differences from the source:
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: "$|n_s|_d=1$, P-a.s. for all $s$" → almost surely, for all $s$ (`∀ᵐ ω, ∀ s`); reason: at fixed times alone, $|n|\neq 1$ at a random jump time would be allowed, and displacement would no longer match the cost
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - encoding: "unique" solution → two solutions are indistinguishable on $[0,T-t]$; reason: the meaning of uniqueness for processes
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, §3, claim after (3.1), p.5

import Mathlib
import Definitions.Def_SingularStopperVI_Assumptions

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, §3, claim after (3.1), p.5.
Under Assumption 3.1, for every `(n,ν) ∈ 𝒜_t` and `x`, equation (3.1) has a solution on `[0,T−t]`, and
two solutions are indistinguishable there. -/
theorem wellPosed_3_1 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {t : ℝ} (ht : t ∈ Icc 0 D.T)
    (x : Euc d) {n : ℝ≥0 → Ω → Euc d} {ν : ℝ≥0 → Ω → ℝ} (hc : IsControl B (horizon D t) n ν) :
    (∃ X, IsStateSol B D (horizon D t) x n ν X) ∧
    ∀ X Y, IsStateSol B D (horizon D t) x n ν X → IsStateSol B D (horizon D t) x n ν Y →
      ∀ᵐ ω ∂B.P, ∀ s ≤ horizon D t, X s ω = Y s ω := by sorry

end SingularStopperVI
