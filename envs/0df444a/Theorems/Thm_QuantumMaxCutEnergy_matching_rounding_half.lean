-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_rounding_half
-- name    : QuantumMaxCutEnergy.matching_rounding_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T17:42:54.959037+00:00
-- url     : https://prove2.me/theorems/c375af2d-9f3e-4316-b188-fdbfd27b5c4d
-- title:
--   Fractional-matching half-rounding: a matching carries half the $w \\cdot x$ mass
-- statement:
--   A fractional-matching rounding lemma for weighted graphs, phrased over the campaign's `QuantumMaxCutEnergy` model.
--
--   Let $G = (V, E, w)$ be a finite graph with nonnegative rational edge weights, and let $x : E \to \mathbb{R}_{\ge 0}$ assign a nonnegative mass to every edge such that the total incident mass at every vertex is at most $1$:
--
--   $$\forall i \in V, \quad \sum_{j \ne i} x_{ij} \le 1.$$
--
--   (Here $x_{ij}$ denotes the mass of the edge between $i$ and $j$, and absent edges carry mass $0$.) Then there exists a matching $M$ — a set of pairwise vertex-disjoint edges — whose total weight is at least **half** of the total $w \cdot x$ mass:
--
--   $$\exists M \text{ matching in } G, \qquad \tfrac{1}{2} \sum_{e \in E} w_e \, x_e \le \sum_{e \in M} w_e.$$
--
--   **Role in the Quantum Max-Cut campaign.** This is the elementary extraction step behind the matching state of the Lee–Parekh level-2 analysis of Quantum Max-Cut (ICALP 2024). Their positive edge values $h^+_{ij}$ satisfy exactly the star constraint above — proved on this platform as `QuantumMaxCutEnergy.PauliSDP.moment_positive_excess_star` — and a matching of weight proportional to $\sum_e w_e h^+_e$ turns that bound into the matching-state energy $(W + 3m)/2$. The constant obtained by the greedy argument formalized here is $1/2$; the paper's $4/5$ rounding factor goes through Edmonds' b-matching LP integrality and is left as a sharpening.
--
--   **Formalization Note.** The star constraint is written in the vertex-indexed form used by the platform's Pauli-moment relaxation statements: a sum over all $j : \mathsf{Fin}(n)$ with a decidability split on the order of $i$ and $j$, so that each incident edge contributes once. A matching is encoded as a `Finset` of edges with the pairwise four-way endpoint-disjointness condition spelled out.
-- source:
--   Elementary greedy rounding (standard); motivation: Eunou Lee and Ojas Parekh, An Improved Quantum Max Cut Approximation via Matching, ICALP 2024, https://arxiv.org/abs/2401.03616 , Theorem 2 (matching-state analysis; their 4/5 rounding uses the b-matching LP, the 1/2 constant here is self-contained)

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.matching_rounding_half (G : QuantumMaxCutEnergy.Input) (x : QuantumMaxCutEnergy.Edge G.n → ℝ) (hx : ∀ e, 0 ≤ x e) (hstar : ∀ i : Fin G.n, ∑ j : Fin G.n, (if h : i < j then x ⟨(i, j), h⟩ else if h : j < i then x ⟨(j, i), h⟩ else 0) ≤ 1) :
    ∃ M : Finset (QuantumMaxCutEnergy.Edge G.n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧
        e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (1 / 2 : ℝ) * ∑ e, (G.weights e : ℝ) * x e ≤ ∑ e ∈ M, (G.weights e : ℝ) := by sorry
