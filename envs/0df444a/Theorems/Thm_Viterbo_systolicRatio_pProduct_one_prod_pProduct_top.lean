-- Prove2me | Theorems.Thm_Viterbo_systolicRatio_pProduct_one_prod_pProduct_top
-- name    : Viterbo.systolicRatio_pProduct_one_prod_pProduct_top
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:17:48.16182+00:00
-- url     : https://prove2.me/theorems/f2b223ac-41d9-4ec0-93cd-ac91c31b863b
-- title:
--   Haim-Kislev [33], Proposition 5.1.4 — Sys((X₁ ⊗₁ X₂) × (Y₁ ⊗_∞ Y₂)) = Sys(X₁ × Y₁)·Sys(X₂ × Y₂) when the capacities agree
-- statement:
--   Let $m, k \ge 1$, let $X_1, Y_1 \subset \mathbb R^m$ and $X_2, Y_2 \subset \mathbb R^k$ be convex domains containing the origin, and suppose $c_{\rm EHZ}(X_1 \times Y_1) = c_{\rm EHZ}(X_2 \times Y_2)$. Then $\mathrm{Sys}\big((X_1 \otimes_1 X_2) \times (Y_1 \otimes_\infty Y_2)\big) = \mathrm{Sys}(X_1 \times Y_1)\cdot\mathrm{Sys}(X_2 \times Y_2)$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 7, the (1, ∞)-product formula, which cites Haim-Kislev, P., Symplectic invariants and convex bodies, Ph.D. thesis, Tel Aviv University (2024) (no DOI), Proposition 5.1.4

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem systolicRatio_pProduct_one_prod_pProduct_top (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X₁ Y₁ : Set (OAI.SymmetricPolar.Position m)) (X₂ Y₂ : Set (OAI.SymmetricPolar.Position k))
    (hX₁ : IsConvexDomain X₁) (hY₁ : IsConvexDomain Y₁) (hX₂ : IsConvexDomain X₂) (hY₂ : IsConvexDomain Y₂)
    (h₀ : 0 ∈ X₁ ∧ 0 ∈ Y₁ ∧ 0 ∈ X₂ ∧ 0 ∈ Y₂) (hc : cEHZ (X₁ ×ˢ Y₁) = cEHZ (X₂ ×ˢ Y₂)) :
    systolicRatio (pProduct 1 X₁ X₂ ×ˢ pProduct ⊤ Y₁ Y₂) =
      systolicRatio (X₁ ×ˢ Y₁) * systolicRatio (X₂ ×ˢ Y₂) := by
  sorry

end Viterbo
