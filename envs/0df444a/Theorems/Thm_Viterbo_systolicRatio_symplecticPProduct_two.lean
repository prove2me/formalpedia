-- Prove2me | Theorems.Thm_Viterbo_systolicRatio_symplecticPProduct_two
-- name    : Viterbo.systolicRatio_symplecticPProduct_two
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:15:32.587169+00:00
-- url     : https://prove2.me/theorems/66a14d90-82a1-43d7-a595-c0702ed0dbb3
-- title:
--   Haim-Kislev–Ostrover [34], Theorem 1.2 — Sys(X ⊗₂ Y) = Sys(X)·Sys(Y) when c_EHZ(X) = c_EHZ(Y)
-- statement:
--   Let $m, k \ge 1$ and let $X \subset \mathbb R^{2m}$, $Y \subset \mathbb R^{2k}$ be convex domains containing the origin with $c_{\rm EHZ}(X) = c_{\rm EHZ}(Y)$. Then the symplectic 2-product $X \otimes_2 Y \subset \mathbb R^{2(m+k)}$ has $\mathrm{Sys}(X \otimes_2 Y) = \mathrm{Sys}(X)\cdot\mathrm{Sys}(Y)$.
--
--   *Formalization note.* The domains are taken to contain the origin, as the definition of the $p$-product on p. 5 requires ("for two subsets $X \subset \mathbb R^m$ and $Y \subset \mathbb R^n$ containing the origin").
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 5, the 2-product formula, which cites Haim-Kislev, P. and Ostrover, Y., Remarks on symplectic capacities of p-products, Internat. J. Math. 34 (2023) 2350021, https://doi.org/10.1142/S0129167X23500210, Theorem 1.2

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem systolicRatio_symplecticPProduct_two (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X : Set (OAI.SymmetricPolar.Phase m)) (Y : Set (OAI.SymmetricPolar.Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y)
    (hXY : cEHZ X = cEHZ Y) :
    systolicRatio (symplecticPProduct 2 X Y) = systolicRatio X * systolicRatio Y := by
  sorry

end Viterbo
