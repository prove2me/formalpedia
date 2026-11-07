-- Prove2me | Theorems.Thm_SecondBestBT_lemma_5_12
-- name    : SecondBestBT.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:45.344204+00:00
-- url     : https://prove2.me/theorems/3d17b8a1-c5cd-4f5e-bac9-58db006f06c1
-- title:
--   Lemma 5.12 — finite-pair fixed-multiplier bound
-- statement:
--   Fix $W\in\mathbb Z_{\ge0}$, $\alpha\ge0$, and priors $F_S,F_B\in\Delta(Z_W)$, retaining zero-mass grid reports. Then
--   $$
--   \max_{x\in R_3(W)}\Big[\mathrm{GFT}(x)+\alpha\,\Lambda_D(x)-\tfrac12\,\mathrm{FB}\Big]\ \ge\ 0,
--   $$
--   that is, the maximum over $R_3(W)$ is attained and is nonnegative.
--
--   Combined with Lemma 4.1 and $R_3(W)\subseteq R_1(W)$, it gives $\mathrm{SB}\ge\frac12\mathrm{FB}$ on every finite integer grid.
--
--   Differences from the source:
--   - encoding: $\max_{x\in R_3(W)}[\dots]\ge0$ → some $x\in R_3(W)$ maximizes the objective over $R_3(W)$ and its value is $\ge0$; reason: the printed max presupposes attainment
--   - encoding: allocations $x:Z_W^2\to[0,1]$ → matrices `ℕ → ℕ → ℝ` constrained and evaluated only at indices $\le W$; reason: entries above $W$ enter no sum and no constraint
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 5.12, p.24

import Mathlib
import Definitions.Def_SecondBestBT_IsGridPMF
import Definitions.Def_SecondBestBT_gftZ
import Definitions.Def_SecondBestBT_lambdaZ
import Definitions.Def_SecondBestBT_fbZ
import Definitions.Def_SecondBestBT_R3

namespace SecondBestBT

/-- **Lemma 5.12** (finite-pair fixed-multiplier bound; Liu–Qin–Ren–Wang, *Second-Best Bilateral
Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…, Lemma 5.12, p.24). Fix
`W ∈ ℤ_{≥0}`, `α ≥ 0` and `F_S, F_B ∈ ∆(Z_W)`, retaining zero-mass grid reports. Then
`max_{x ∈ R3(W)} [GFT(x) + α Λ_D(x) − ½ FB] ≥ 0`.

**Formalization Note** "max ≥ 0" is stated as: some `x ∈ R3(W)` maximizes the objective over
`R3(W)` and its value is nonnegative. -/
theorem lemma_5_12 (W : ℕ) (α : ℝ) (hα : 0 ≤ α) (fS fB : ℕ → ℝ) (hfS : IsGridPMF fS W)
    (hfB : IsGridPMF fB W) :
    ∃ x ∈ R3 W,
      (∀ y ∈ R3 W, gftZ fS fB W y + α * lambdaZ fS fB W y - 1 / 2 * fbZ fS fB W ≤
        gftZ fS fB W x + α * lambdaZ fS fB W x - 1 / 2 * fbZ fS fB W) ∧
      0 ≤ gftZ fS fB W x + α * lambdaZ fS fB W x - 1 / 2 * fbZ fS fB W := by sorry

end SecondBestBT
