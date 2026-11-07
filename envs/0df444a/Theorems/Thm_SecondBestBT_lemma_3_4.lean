-- Prove2me | Theorems.Thm_SecondBestBT_lemma_3_4
-- name    : SecondBestBT.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:44:42.260607+00:00
-- url     : https://prove2.me/theorems/88bd00dd-6c7a-4841-8d63-2a346bca8099
-- title:
--   Lemma 3.4 — first-best approximation under dyadic rounding
-- statement:
--   For every pair of priors $F_S,F_B$ on $[0,1]$ and every $M\ge1$, the first-best gains from trade of the rounded priors $\hat F^M_S,\hat F^M_B$ (the laws of $\pi^M_S(s)$ and $\pi^M_B(b)$) satisfy
--   $$
--   0\le \mathrm{FB}(F_S,F_B)-\mathrm{FB}(\hat F^M_S,\hat F^M_B)\le 2^{1-M}.
--   $$
--   As $M\to\infty$ the rounded first-best GFT converges to $\mathrm{FB}(F_S,F_B)$, and it is eventually positive whenever $\mathrm{FB}(F_S,F_B)>0$.
--
--   Differences from the source:
--   - encoding: the rounded priors $\hat F^M_S,\hat F^M_B$ → the pushforwards of $F_S,F_B$ under $\pi^M_S,\pi^M_B$; reason: the paper defines them as the distributions of the rounded values
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 3.4, p.7

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_firstBest
import Definitions.Def_SecondBestBT_dyadicRoundS
import Definitions.Def_SecondBestBT_dyadicRoundB

open MeasureTheory Filter Topology

namespace SecondBestBT

/-- **Lemma 3.4** (first-best approximation; Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2
Efficient*, arXiv:2606.03849, held version sha256 17184930…, Lemma 3.4, p.7). For every pair of
priors on `[0, 1]` and every `M ≥ 1`,
`0 ≤ FB(F_S, F_B) − FB(F̂^M_S, F̂^M_B) ≤ 2^{1−M}`. As `M → ∞` the rounded first-best GFT converges
to `FB(F_S, F_B)`, and it is eventually positive whenever `FB(F_S, F_B) > 0`.

**Formalization Note** `F̂^M_S = μS.map π^M_S` and `F̂^M_B = μB.map π^M_B` are the laws of the
rounded values. -/
theorem lemma_3_4 (μS μB : Measure ℝ) (hS : IsPriorOn (Set.Icc 0 1) μS)
    (hB : IsPriorOn (Set.Icc 0 1) μB) :
    (∀ M : ℕ, 1 ≤ M →
      0 ≤ firstBest μS μB - firstBest (μS.map (dyadicRoundS M)) (μB.map (dyadicRoundB M)) ∧
      firstBest μS μB - firstBest (μS.map (dyadicRoundS M)) (μB.map (dyadicRoundB M)) ≤
        (2 : ℝ) ^ ((1 : ℤ) - M)) ∧
    Tendsto (fun M : ℕ => firstBest (μS.map (dyadicRoundS M)) (μB.map (dyadicRoundB M)))
      atTop (𝓝 (firstBest μS μB)) ∧
    (0 < firstBest μS μB →
      ∀ᶠ M : ℕ in atTop, 0 < firstBest (μS.map (dyadicRoundS M)) (μB.map (dyadicRoundB M))) := by sorry

end SecondBestBT
