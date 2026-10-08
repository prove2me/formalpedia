-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_compound_nonstationary_palm
-- name    : ServiceParts.NonstatPalm.compound_nonstationary_palm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:57:36.147545+00:00
-- url     : https://prove2.me/theorems/eaf30f66-9070-470c-81ce-7b02f1810d9f
-- title:
--   Theorem 14 — with nonstationary compound Poisson demand, units in resupply at t are compound Poisson with mean α(t)
-- statement:
--   In the single-location model with nonstationary compound Poisson demand, where all units of an order placed at time $s$ share the order's resupply time with distribution function $G_s$, let $X(t)$ be the number of units in resupply at time $t$, $\alpha(t) = \int_0^t (1 - G_s(t-s))\lambda(s)\,ds$, and $u^{(n)}_k$ the $n$-fold convolution of the order-size distribution. For every $t \ge 0$,
--   $$P[X(t) = k] = \sum_{n \ge 1} u^{(n)}_k\, e^{-\alpha(t)}\,\frac{\alpha(t)^n}{n!}, \qquad k \ge 1,$$
--   and $P[X(t) = 0] = e^{-\alpha(t)}$.
--
--   So the number of units in resupply is compound Poisson: a Poisson($\alpha(t)$) number of orders in resupply, compounded by the order-size distribution.
--
--   **Formalization Note** The book prints the formula for every $k$, but its sum starts at $n = 1$ and orders are for at least one unit, so at $k = 0$ it would give $0$; the event "no order in resupply" has probability $e^{-\alpha(t)}$ (the $n = 0$ term). The statement gives the book's formula for $k \ge 1$ and the correct value at $k = 0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 218, Theorem 14

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem compound_nonstationary_palm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : CompoundResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ k : ℕ, 1 ≤ k →
      (P {ω | S.unitsInResupply t ω = k}).toReal =
        ∑' n : ℕ, ServiceParts.Palm.convPow S.sizeProb (n + 1) k *
          (Real.exp (-S.alpha t) * S.alpha t ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))) ∧
    (P {ω | S.unitsInResupply t ω = 0}).toReal = Real.exp (-S.alpha t) := by sorry

end ServiceParts.NonstatPalm
