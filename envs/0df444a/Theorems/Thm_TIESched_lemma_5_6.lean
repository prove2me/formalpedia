-- Prove2me | Theorems.Thm_TIESched_lemma_5_6
-- name    : TIESched.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:43.597298+00:00
-- url     : https://prove2.me/theorems/16ee8014-e126-4e60-bd00-521b4cba56a4
-- title:
--   Lemma 5.6 — padding-invariant replacement
-- statement:
--   Every feasible, truthful, $\Gamma$-approximate fractional mechanism family admits a feasible, truthful, $\Gamma$-approximate fractional mechanism family $(\hat x,\hat u)$, with finite implementing payments, that is invariant under every padding-appending operation:
--   $$T_v(\hat x)=\hat x,\qquad T_v(\hat u)=\hat u\qquad\text{for every }v\in\mathbb R^m_{\ge0}\text{ with }\min_i v_i=0.$$
--
--   The invariance gives the zero boundary condition of Lemma 5.7.
--
--   Differences from the source:
--   - generalization: invariance under T_v defined with one chosen fresh label per job set → invariance for every fresh label k ∉ S; reason: the replacement constructed in the proof is relabeling-equivariant, so the identities hold for every label (p.24); the Lean statement implies the source's
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.6, p.23

import Mathlib
import Definitions.Def_TIESched_PaddingInvariant

set_option autoImplicit false

namespace TIESched

/-- **Lemma 5.6 (Padding-invariant replacement)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 5.6,
p.23). Every truthful, Γ-approximate fractional mechanism family `(x, u)` admits a truthful,
Γ-approximate fractional replacement `(x̂, û)` with finite implementing payments that is invariant
under every padding-appending operation: `T_v(x̂) = x̂`, `T_v(û) = û` for every `v ∈ ℝ^m_{≥0}` with
`min_i v_i = 0`.

**Formalization Note.** Families are `FracMech m` (allocation and real, hence finite, payments);
`u` is the normalized utility. `PaddingInvariant` requires the identities for every fresh label. -/
theorem lemma_5_6 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (Γ : ℝ) (M : FracMech m)
    (hfeas : Feasible M.alloc) (htr : Truthful M) (happ : IsApprox M Γ) :
    ∃ M' : FracMech m, Feasible M'.alloc ∧ Truthful M' ∧ IsApprox M' Γ ∧ PaddingInvariant M' := by sorry

end TIESched
