-- Prove2me | Theorems.Thm_ProphetBipartite_eq_11_lower_bound
-- name    : ProphetBipartite.eq_11_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:54.723295+00:00
-- url     : https://prove2.me/theorems/9cb53d4c-800d-480a-9ec0-38cca0c8d1fc
-- title:
--   Display (11) — the min over vertex sets lower-bounds $\mathbb E[\mathrm{V\text{-}add}(l,r)]$
-- statement:
--   Let the edge values be independent with finite means, $\mathrm{opt}$ an optimal matching selector with matrices $M,Q$ of (10), $\sigma$ an arrival order, and $l\in\mathbb R_{\ge0}^L$, $r\in\mathbb R_{\ge0}^R$. Then
--
--   $$
--   \mathbb E_v\big[\mathrm{V\text{-}add}(l,r)\big]\ \ge\ \min_{S_L\subseteq L,\ S_R\subseteq R}\Big(\sum_{i\in S_L}l_i+\sum_{j\in S_R}r_j+\sum_{i\notin S_L}\sum_{j\notin S_R}\big[M_{i,j}-(l_i+r_j)\,Q_{i,j}\big]^+\Big).
--   $$
--
--   The right-hand side no longer refers to the run: the covered sets $X_L(v)$, $X_R(v)$ of the bound (8) have been replaced by worst-case sets $S_L$, $S_R$ (bound (9)), and the inner expectations by $M$ and $Q$. This is the linear-algebraic form in which the prices are then optimized.
--
--   Differences from the source:
--   - reading: V-add is described by "two positive real vectors" l, r (p.5) → prices l : L → ℝ≥0, r : R → ℝ≥0 (zero allowed); reason: the proof of Theorem 3.1 (p.9) finds "non negative price vectors" and Algorithm 1 may start at 0-vectors (p.10); a solution of (17) can have zero coordinates, so "positive" means nonnegative
--   - generalization: opt(v̂) is "a random optimal matching" with unspecified tie-breaking (p.6) → every opt with IsOptSelector (a maximum-value matching for each v, measurable level sets); reason: the paper fixes no tie-breaking rule; every concrete rule is an instance (a measurable one exists: first maximizer in a fixed enumeration)
--   - encoding: values drawn from distributions F_e on ℝ₊ (p.4), with M of (10) a real matrix → laws μ e on ℝ≥0 with ∫⁻ x ∂μ e ≠ ⊤ (finite means); reason: the paper's standing assumption: M (10) and opt = 1ᵀM1 (12) are real numbers only when the means are finite
--   - encoding: v ∼ F = ∏_e F_e, independent edge values (p.4) → the product measure Measure.pi μ on E → ℝ≥0; reason: Lean convention; same instances
--   - encoding: bipartite multi-graph G(L, R) with multi-edges E (p.4) → finite types L, R, E with endpoint maps left : E → L, right : E → R; M_ij, Q_ij aggregate the parallel edges from i to j; reason: Lean convention; parallel edges are distinct elements of E, and at most one lies in a matching
--   - encoding: expectations E_v[·] → real Bochner integrals ∫ … ∂(Measure.pi μ); reason: with finite means every integrand is integrable; same values
--   - encoding: min over S_L, S_R → Finset.inf' over the finite nonempty set of pairs (S_L, S_R) of finsets; reason: Lean convention; same value
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, display (11), p.8 (from (8), (9))

import Mathlib
import Definitions.Def_ProphetBipartite_IsOrder
import Definitions.Def_ProphetBipartite_vaddRun
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal ENNReal

namespace ProphetBipartite

/-- **Display (11): the linear-algebraic lower bound on `V-add(l, r)`.** Gravin & Wang,
arXiv:1902.06243v1, §3.2, (11), p.8: for any prices `l, r ≥ 0` and any arrival order,

`E_v[V-add(l, r)] ≥ min_{S_L ⊆ L, S_R ⊆ R} ( ∑_{i∈S_L} l_i + ∑_{j∈S_R} r_j + ∑_{i∉S_L, j∉S_R} [M_{i,j} − (l_i + r_j)·Q_{i,j}]⁺ )`,

with `M`, `Q` the matrices of (10).

**Formalization Note.** The minimum is `Finset.inf'` over the finite nonempty set of pairs
`(S_L, S_R)`. Edge values are independent with laws `μ e` on `ℝ≥0` with finite means; the bound
holds for every measurable optimal matching selector `opt`. The expectation is a real integral. -/
theorem eq_11_lower_bound {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (hσ : IsOrder σ) :
    (Finset.univ : Finset (Finset L × Finset R)).inf' Finset.univ_nonempty
        (fun S => ∑ i ∈ S.1, (l i : ℝ) + ∑ j ∈ S.2, (r j : ℝ) +
          ∑ i ∈ S.1ᶜ, ∑ j ∈ S.2ᶜ,
            max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0) ≤
      ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) := by sorry

end ProphetBipartite
