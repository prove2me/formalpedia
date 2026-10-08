-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_lemma_4
-- name    : PeakEndPricing.Convergence.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:38.426064+00:00
-- url     : https://prove2.me/theorems/fa0b9bff-ab75-4ec5-bfa0-e1ba3bfab2ea
-- title:
--   Lemma 4 — Problem (8) has a unique steady state, solving (11); every m ∈ [s, S] is a steady state for some ν
-- statement:
--   Under the standing hypotheses of Section 3, let $s, S \in \mathbf P$ be roots of (9) and (10):
--   $$\pi_0'(s) - \lambda(1-\beta(1-\theta))s = 0, \qquad \pi_0'(S) - \gamma(1-\beta)S = 0.$$
--   A steady state of the smooth Problem (8) with parameters $\nu$, $m$ is a price $p\in\mathbf P$ from which the constant path $p_t\equiv p$ attains $J^\nu_m(p)$. Then:
--
--   1. (a) for every $\nu\in[0,1]$ and $m\in\mathbf P$, Problem (8) has exactly one steady state, and every steady state $p$ solves
--   $$\pi_0'(p) - \big[\lambda(1-\nu)(2-(1-\theta)(1+\beta)) + \nu\gamma(1-\beta)\big]p + \lambda(1-\nu)\theta m = 0; \qquad (11)$$
--   2. (b) for every $m\in[s,S]$ there is $\nu\in[0,1]$ such that $m$ is a steady state of the corresponding Problem (8).
--
--   Part (a) defines $p^{**}_\lambda(m)$ (the steady state for $\nu = 0$, which solves (12)); part (b) shows that the bounds of Lemma 3 can be tuned to have any $m\in[s,S]$ as a steady state.
--
--   **Formalization Note** The paper writes "the thresholds $s, S$ solve (9), (10)"; here $s$ and $S$ are given numbers in $\mathbf P$ carried with these equations as hypotheses (the roots are unique since the left-hand sides are strictly decreasing). Steady states are optimal constant paths; (11) is a conclusion, not the definition.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 11, Lemma 4 (with (8)–(10), pp. 10–11)

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem lemma_4 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) :
    (∀ nu ∈ Set.Icc (0 : ℝ) 1, ∀ m ∈ Set.Icc (0 : ℝ) pbar,
      (∃! p : ℝ, IsAuxSteadyState pbar d0 lam gam theta beta m nu p) ∧
      ∀ p : ℝ, IsAuxSteadyState pbar d0 lam gam theta beta m nu p →
        eq11 d0 lam gam theta beta m nu p) ∧
    (∀ m ∈ Set.Icc s S, ∃ nu ∈ Set.Icc (0 : ℝ) 1,
      IsAuxSteadyState pbar d0 lam gam theta beta m nu m) := by sorry

end PeakEndPricing.Convergence
