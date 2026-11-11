-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_10
-- name    : ProdMixedTomo.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:45.948117+00:00
-- url     : https://prove2.me/theorems/86ffd1cd-96b9-4424-903d-4cdb9479f72c
-- title:
--   Lemma 4.10 — test sets for $\nu$ rescale into test sets for $\mu$
-- statement:
--   Let $\mu,\nu\in[0,1]^n$ and $\eta=\|\nu-\mu\|_\nu$. Then
--   1. $y\in T_\nu$ implies $y/\sqrt{1+\eta}\in T_\mu$;
--   2. $M\in\mathcal T_\nu$ implies $M/(1+\eta)\in\mathcal T_\mu$.
--
--   It lets the analysis move between the test sets of the true mean and of the current weighted mean at a cost controlled by their distance.
--
--   Differences from the source:
--   - encoding: μ implicit (Definition 4.6) → explicit hypothesis μ ∈ [0,1]ⁿ; reason: the domain on which T_μ and 𝒯_μ are defined
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.10, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_TestNorms

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.10, p.26 (PDF p.28). If `ν ∈ [0,1]ⁿ` and `η = ‖ν − μ‖_ν`, then `y ∈ T_ν` implies
`y/√(1+η) ∈ T_μ`, and `M ∈ 𝒯_ν` implies `M/(1+η) ∈ 𝒯_μ` (for `μ ∈ [0,1]ⁿ`, Definition 4.6). -/
theorem lemma_4_10 (n : ℕ) (μ ν : Fin n → ℝ) (hμ : μ ∈ MeanBox n) (hν : ν ∈ MeanBox n) :
    (∀ y ∈ Tset ν, (Real.sqrt (1 + vnorm ν (ν - μ)))⁻¹ • y ∈ Tset μ) ∧
    (∀ M ∈ TTset ν, (1 + vnorm ν (ν - μ))⁻¹ • M ∈ TTset μ) := by sorry

end ProdMixedTomo
