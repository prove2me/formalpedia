-- Prove2me | Theorems.Thm_PolyVoting_dirichlet_marginal
-- name    : PolyVoting.dirichlet_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:22.367245+00:00
-- url     : https://prove2.me/theorems/c0009bec-0f61-463d-aa1a-7437ced2e59e
-- title:
--   p.10 — the marginals of $\mathrm{Dir}(a_1,\dots,a_K)$ are Beta
-- statement:
--   If $(x_1,\dots,x_K)$ has the law $\mathrm{Dir}(a_1,\dots,a_K)$, then for each $k\in[K]$,
--   $$x_k\overset{d}{=}\mathrm{Beta}\Big(a_k,\sum_{j\ne k}a_j\Big).$$
--
--   This identifies the limit law of one bidder's share.
--
--   Differences from the source:
--   - encoding: Dir has a density on the simplex in ℝ^K → pushforward under y ↦ (y, 1 − Σy) of the density on the first K − 1 coordinates (point mass at 1 for K = 1); reason: the simplex is a Lebesgue null set of ℝ^K; this is the standard meaning of the density; dirichletMeasure_two in the verification file checks K = 2 against Beta
--   - encoding: parameters a_1, …, a_K of Dir with K bidders → 2 ≤ K and 0 < a j; reason: the guard only excludes undefined laws: at K = 1 the second Beta parameter is an empty sum
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, §2.2, p.10, "It is easily seen that if (x1, . . . , xK) =d Dir(a1, . . . , aK) then for each k ∈ [K], xk =d Beta(ak, Σ_{j≠k} aj)"

import Mathlib
import Definitions.Def_PolyVoting_dirichletMeasure

open MeasureTheory ProbabilityTheory

namespace PolyVoting

/-- **The marginals of a Dirichlet law are Beta** (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.10): if `x ~ Dir(a₁, …, a_K)` then `x_k ~ Beta(a_k, ∑_{j ≠ k} a_j)`.

**Formalization Note.** `2 ≤ K` and `0 < a j` are the parameters for which both laws are defined:
for `K = 1` the second Beta parameter is `0`, and Mathlib's `betaMeasure a 0` is the zero measure. -/
theorem dirichlet_marginal {K : ℕ} (hK : 2 ≤ K) (a : Fin K → ℝ) (ha : ∀ j, 0 < a j) (k : Fin K) :
    (dirichletMeasure a).map (fun x => x k) =
      betaMeasure (a k) (∑ j ∈ Finset.univ.erase k, a j) := by sorry

end PolyVoting
