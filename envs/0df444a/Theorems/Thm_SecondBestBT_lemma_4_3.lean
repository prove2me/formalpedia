-- Prove2me | Theorems.Thm_SecondBestBT_lemma_4_3
-- name    : SecondBestBT.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:51.359341+00:00
-- url     : https://prove2.me/theorems/57f7ba4e-b671-4865-bd7e-bac6187662e2
-- title:
--   Lemma 4.3 — pointwise monotonicity without loss
-- statement:
--   For every $W$, every pair of priors $F_S,F_B\in\Delta(Z_W)$ (zero masses retained) and every $\alpha\ge0$,
--   $$
--   \sup_{x\in R_1(W)}\big[\mathrm{GFT}(x)+\alpha\Lambda_D(x)\big]=\sup_{x\in R_2(W)}\big[\mathrm{GFT}(x)+\alpha\Lambda_D(x)\big].
--   $$
--   Restricting from monotone interims to pointwise-monotone allocations does not change the optimized Lagrangian value.
--
--   Differences from the source:
--   - encoding: the suprema → `sSup` in $\mathbb R$; reason: both sets are nonempty (zero allocation, $R_2(W)\subseteq R_1(W)$) and bounded above (finite cube)
--   - encoding: allocations $x:Z_W^2\to[0,1]$ → matrices `ℕ → ℕ → ℝ` constrained and evaluated only at indices $\le W$; reason: entries above $W$ enter no sum and no constraint
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 4.3, p.9

import Mathlib
import Definitions.Def_SecondBestBT_IsGridPMF
import Definitions.Def_SecondBestBT_gftZ
import Definitions.Def_SecondBestBT_lambdaZ
import Definitions.Def_SecondBestBT_R1
import Definitions.Def_SecondBestBT_R2

namespace SecondBestBT

/-- **Lemma 4.3** (pointwise monotonicity without loss; Liu–Qin–Ren–Wang, *Second-Best Bilateral
Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…, Lemma 4.3, p.9). For
every `W`, every `F_S, F_B ∈ ∆(Z_W)` and every `α ≥ 0`,
`sup_{x ∈ R1(W)} [GFT(x) + α Λ_D(x)] = sup_{x ∈ R2(W)} [GFT(x) + α Λ_D(x)]`.

**Formalization Note** Both suprema are `sSup` in `ℝ` of nonempty sets (the zero allocation lies
in `R2(W) ⊆ R1(W)`) bounded above (the allocation cube is bounded). Zero masses are retained. -/
theorem lemma_4_3 (W : ℕ) (fS fB : ℕ → ℝ) (hfS : IsGridPMF fS W) (hfB : IsGridPMF fB W)
    (α : ℝ) (hα : 0 ≤ α) :
    sSup ((fun x => gftZ fS fB W x + α * lambdaZ fS fB W x) '' R1 fS fB W) =
      sSup ((fun x => gftZ fS fB W x + α * lambdaZ fS fB W x) '' R2 W) := by sorry

end SecondBestBT
