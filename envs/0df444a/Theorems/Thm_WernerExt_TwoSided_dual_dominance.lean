-- Prove2me | Theorems.Thm_WernerExt_TwoSided_dual_dominance
-- name    : WernerExt.TwoSided.dual_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:41.449029+00:00
-- url     : https://prove2.me/theorems/3212d0a9-6c5a-416f-ba46-56ffd5f630f4
-- title:
--   SM Eq. (14), Supplemental Material p. 3 — the M-dual preserves dominance order: λ ⊵ μ implies λ̄ ⊵ μ̄
-- statement:
--   Let $d\ge2$, $\lambda,\mu\vdash_dn$ with $\lambda\trianglerighteq\mu$, and let $M\ge\lambda_1,\mu_1$. With the $M$-duals $\bar\lambda_i=M-\lambda_{d-i+1}$, $\bar\mu_i=M-\mu_{d-i+1}$,
--   $$\bar\lambda\ \trianglerighteq\ \bar\mu.$$
--
--   So the dominance order between duals is the one between the original partitions, which the paper uses to transfer the Azenhas bound to the minimum product diagram.
--
--   **Formalization Note** $M\ge\lambda_1,\mu_1$ is written as $M\ge\lambda_i,\mu_i$ for every $i$ (equivalent for decreasing rows); the dual is computed with natural-number subtraction, exact under this hypothesis.
--
--   Differences from the source:
--   - encoding: M ≥ λ_1 (and μ_1) → ∀ i, λ_i ≤ M ∧ μ_i ≤ M; reason: equivalent for weakly decreasing rows
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, Supplemental Material p. 3 (PDF 9), SM Eq. (14)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

/-- SM Eq. (14), SM p. 3: taking the `M`-dual preserves dominance order: if `λ, μ ⊢_d n`,
`λ ⊵ μ` and `M` is at least the first rows of both, then `λ̄ ⊵ μ̄`. -/
theorem dual_dominance (d n M : ℕ) (hd : 2 ≤ d) (l m : DPart d n) (hlm : Dominates l.1 m.1)
    (hM : ∀ i : Fin d, l.1 i ≤ M ∧ m.1 i ≤ M) :
    Dominates (mDual M l.1) (mDual M m.1) := by sorry

end WernerExt.TwoSided
