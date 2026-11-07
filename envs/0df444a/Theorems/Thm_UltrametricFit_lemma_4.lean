-- Prove2me | Theorems.Thm_UltrametricFit_lemma_4
-- name    : UltrametricFit.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:10.708254+00:00
-- url     : https://prove2.me/theorems/0dc260ce-b6b8-4219-b29d-b3b087850a0c
-- title:
--   Lemma 4 ([HKM05]), p.6 — restricting to the input's distance values loses a factor of $2$
-- statement:
--   Let $X$ be an instance. For each $p\ge1$ the minimum $\min_{U'}\|U'-X\|_p$ over all ultrametrics $U'$ is attained, and there is an ultrametric $U$ with $U(i,j)\in\{D_1,\dots,D_L\}$ for all $i\ne j$ such that
--   $$\|U-X\|_p\le2\,\|U'-X\|_p\qquad\text{for every ultrametric }U'.$$
--   For $p=1$ there is such a $U$ with $\|U-X\|_1\le\|U'-X\|_1$ for every ultrametric $U'$, that is, $U$ attains the minimum over all ultrametrics.
--
--   The result justifies working only with ultrametrics whose values are the $D_\ell$, which is what the LP can represent. The paper cites it from Harb, Kannan and McGregor and does not prove it.
--
--   Differences from the source:
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
--   - encoding: $\le2\min_{U'}\|U'-X\|_p$ and $=\min_{U'}\|U'-X\|_1$ → a bound against every ultrametric $U'$; reason: no real infimum occurs; the attainment of the minimum for every $p$ is a separate clause; since $U$ is itself an ultrametric, the $p=1$ clause is the printed equality with the minimum attained
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Lemma 4, p.6

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_layerValue

namespace UltrametricFit

/-- **Lemma 4 ([HKM05])**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.6,
both clauses: there is an ultrametric `U` with values in `{D_1, …, D_L}` and
`‖U − X‖_p ≤ 2 · min_{U'} ‖U' − X‖_p`, and for `p = 1` one with `‖U − X‖_1 = min_{U'} ‖U' − X‖_1`.

**Formalization Note.** The minimum is written as a bound against every ultrametric `U'`, so no
real infimum occurs, and its attainment for every `p ≥ 1` (the page writes `min_{U'}`) is stated
as a separate clause: some ultrametric `U⋆` is at least as close to `X` as every ultrametric. In the
last clause `U` is itself an ultrametric, so it attains the minimum over all ultrametrics, which is
the printed equality. The paper cites this result and does not prove it. -/
theorem lemma_4 {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X) :
    (∀ p : ℝ, 1 ≤ p → (∃ Ustar, IsUltrametric Ustar ∧
      ∀ U', IsUltrametric U' → lpDist p Ustar X ≤ lpDist p U' X) ∧ ∃ U, IsUltrametric U ∧
      (∀ i j, i ≠ j → ∃ ℓ ∈ Finset.Icc 1 (numLayers X), U i j = layerValue X ℓ) ∧
      ∀ U', IsUltrametric U' → lpDist p U X ≤ 2 * lpDist p U' X) ∧
    (∃ U, IsUltrametric U ∧
      (∀ i j, i ≠ j → ∃ ℓ ∈ Finset.Icc 1 (numLayers X), U i j = layerValue X ℓ) ∧
      ∀ U', IsUltrametric U' → lpDist 1 U X ≤ lpDist 1 U' X) := by sorry

end UltrametricFit
