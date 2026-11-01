-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_single_edge_mixture_reduction_ESA2025
-- name    : QuantumMaxCutEnergy.single_edge_mixture_reduction_ESA2025
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T00:54:58.28171+00:00
-- url     : https://prove2.me/theorems/51dc16b9-dda4-4480-adc9-538681f11ef5
-- title:
--   Averaging reduction to a single edge
-- statement:
--   Let $E$ be a finite edge set with nonnegative weights $w_e$, and let $A$ be finitely many candidates with gains $g_{a,e}$. Fix nonnegative probabilities $\mu_a$ summing to one. If $\alpha\ge0$, $\mathrm{OPT}\le\sum_e w_e b_e$, and $\alpha b_e\le\sum_a\mu_a g_{a,e}$ on each edge, then
--
--   $$\exists a\in A:\quad \alpha\,\mathrm{OPT}\le\sum_e w_e g_{a,e}.$$
--
--   This formalizes the finite averaging implication in the published Lemma 10, without assuming a continuous minimum is attained.
-- source:
--   Apte, Lee, Marwaha, Parekh, and Sud, Improved Algorithms for Quantum MaxCut via Partially Entangled Matchings, ESA 2025, Lemma 10 and its printed proof, pp. 101:11–101:12. https://doi.org/10.4230/LIPIcs.ESA.2025.101 . Scope: the finite, division-free averaging implication for a fixed distribution; no claim of a completed SDP algorithm or continuous min–max attainment.

import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.single_edge_mixture_reduction_ESA2025
    {E A : Type*} (edges : Finset E) (candidates : Finset A)
    (w b : E → ℝ) (gain : A → E → ℝ) (μ : A → ℝ) (opt α : ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hμ : ∀ a ∈ candidates, 0 ≤ μ a)
    (hμsum : ∑ a ∈ candidates, μ a = 1)
    (hα : 0 ≤ α)
    (hopt : opt ≤ ∑ e ∈ edges, w e * b e)
    (hedge : ∀ e ∈ edges, α * b e ≤ ∑ a ∈ candidates, μ a * gain a e) :
    ∃ a ∈ candidates, α * opt ≤ ∑ e ∈ edges, w e * gain a e := by sorry
