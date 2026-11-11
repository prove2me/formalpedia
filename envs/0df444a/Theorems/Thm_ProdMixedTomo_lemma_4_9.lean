-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_9
-- name    : ProdMixedTomo.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:53.652232+00:00
-- url     : https://prove2.me/theorems/72d3e8f3-d297-4c5c-b972-ae1e6d5edb62
-- title:
--   Lemma 4.9 — $\|\delta\delta^\top\|_\mu=O(\|\delta\|_\mu^2)$
-- statement:
--   For $\mu\in[0,1]^n$ and every vector $\delta\in\mathbb R^n$,
--   $$
--   \|\delta\delta^\top\|_\mu\ \le\ C\,\|\delta\|_\mu^2
--   $$
--   for a universal constant $C$, where the left side is the matrix dual norm over $\mathcal T_\mu$ and the right side the vector dual norm over $T_\mu$. It bounds the rank-one terms that appear when re-centering empirical second moments.
--
--   Differences from the source:
--   - encoding: O(·) / ≲ / Ω(·) → ∃ C > 0 chosen before n, μ and δ; reason: meaning of a universal constant (p.13)
--   - encoding: μ implicit (Definition 4.6: μ ∈ ℝⁿ with 0 ≤ μᵢ ≤ 1) → explicit hypothesis μ ∈ [0,1]ⁿ; reason: the domain on which T_μ and 𝒯_μ are defined
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.9, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_TestNorms

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.9, p.25 (PDF p.27). For every `δ ∈ ℝⁿ`, `‖δδᵀ‖_μ = O(‖δ‖²_μ)` (matrix dual norm over
`𝒯_μ` on the left, vector dual norm over `T_μ` on the right), for `μ ∈ [0,1]ⁿ` (Definition 4.6). -/
theorem lemma_4_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (μ δ : Fin n → ℝ), μ ∈ MeanBox n →
      mnorm μ (Matrix.vecMulVec δ δ) ≤ C * vnorm μ δ ^ 2 := by sorry

end ProdMixedTomo
