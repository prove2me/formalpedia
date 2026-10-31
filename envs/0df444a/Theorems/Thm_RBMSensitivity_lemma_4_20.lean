-- Prove2me | Theorems.Thm_RBMSensitivity_lemma_4_20
-- name    : RBMSensitivity.lemma_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:06.000127+00:00
-- url     : https://prove2.me/theorems/aa632c42-9c67-43fb-8460-b6ef792499ab
-- title:
--   Lemma 4.20 — uniform contraction of products of derivative projections
-- statement:
--   Let the data satisfy Assumptions 2.2, 2.4 and 2.5, and let $U_0$ be a compact subset of $U$. There exists $\delta_0\in[0,1)$ such that if $\alpha\in U_0$, $K\in\mathbb N$ and $\{x_k\}_{k=1,\dots,K}$ is a finite sequence in $\partial G$ satisfying $\mathcal I=\bigcup_{k=1,\dots,K}\mathcal I(x_k)$, then for all $y\in\mathbb R^J$,
--   $$\|\mathcal L^\alpha_{x_K}\cdots\mathcal L^\alpha_{x_1}y\|_{B^\alpha}\le\delta_0\|y\|_{B^\alpha}.$$
--
--   Each single projection is only nonexpansive. A product that visits every face is a strict contraction, uniformly on compact parameter sets, and this is the source of stability of the derivative process.
--
--   Differences from the source:
--   - encoding: ‖y‖_{B^α} := min{r ≥ 0 : y ∈ rB^α} → gauge (B α) y; reason: B^α is compact, convex, symmetric with 0 in its interior; same function
--   - encoding: the operator L_x^α of Lemma 4.18 → any functions L with L y ∈ H_x and L y - y ∈ span[d(α,x)]; reason: Lemma 4.18 says exactly one such function exists
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Lemma 4.20, (4.12), p.15

import Mathlib
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_ContractionBound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Lemma 4.20**: arXiv:1907.00472v2, p.15. Let `U₀` be a compact subset of `U`. There exists
`δ₀ ∈ [0, 1)` such that (4.12) holds on `U₀`.

**Formalization Note.** §4 assumes 2.2, 2.4, 2.5 throughout (p.11). The bound is `Data.ContractionBound`.
-/
theorem lemma_4_20 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    {U₀ : Set ℝ} (hU₀ : IsCompact U₀) (hU₀U : U₀ ⊆ D.U) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧ D.ContractionBound B U₀ δ₀ := by sorry

end RBMSensitivity
