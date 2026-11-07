-- Prove2me | Theorems.Thm_SecondBestBT_theorem_4_10
-- name    : SecondBestBT.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:21.218563+00:00
-- url     : https://prove2.me/theorems/a8a658d5-6c64-46a9-a5ca-ac60e56e3a7d
-- title:
--   Theorem 4.10 — guarantee of the greedy construction
-- statement:
--   Fix $\alpha,\beta\ge0$ and an $\alpha$-weakly regular seller prior $F_S$ with full support on $\{0,1,\dots,K\}$ for some $K\ge0$. If Algorithm 1 never returns fail, the allocation rule $x$ it defines satisfies
--   $$
--   x\in R_3,\qquad H(b;x)\ge0\quad\text{for every } b\in\mathbb Z_{\ge0}.
--   $$
--   Consequently, for every buyer prior $F_B$ on $\mathbb Z_{\ge0}$ with finite first-best GFT, the series defining $\mathrm{GFT}(x)$ and $\Lambda_D(x)$ converge absolutely and
--   $$
--   \mathrm{GFT}(x)+\alpha\,\Lambda_D(x)-\beta\,\mathrm{FB}\ \ge\ 0,
--   $$
--   so in particular $\sup_{x\in R_3}\inf_{F_B\in\Delta(\mathbb Z_{\ge0})}\big[\mathrm{GFT}(x)+\alpha\Lambda_D(x)-\beta\,\mathrm{FB}\big]\ge0$.
--
--   The greedy allocation is a buyer-independent certificate: one allocation works for every buyer prior.
--
--   Differences from the source:
--   - generalization: "Consequently, $\sup_{x\in R_3}\inf_{F_B}[\dots]\ge0$" → the inequality for the algorithm's own output $x$ and every buyer prior with finite FB; reason: the output lies in $R_3$, so the statement implies the printed sup–inf
--   - reading: $\inf$ over $F_B\in\Delta(\mathbb Z_{\ge0})$ → every buyer prior on $\mathbb Z_{\ge0}$ with finite first-best GFT; reason: the paper's standing condition FB $<\infty$ (pp.5, 13): "every buyer prior on $\mathbb Z_{\ge0}$ with finite first-best GFT"
--   - encoding: $\mathrm{GFT}$, $\Lambda_D$, $\mathrm{FB}$ for a buyer prior with infinite support → series over $(s,b)\in\mathbb N\times\mathbb N$ of the expanded summands, with $1-F_B(b)$ for $\sum_{b'>b}f_B(b')$; summability of GFT and $\Lambda_D$ is part of the conclusion; reason: the paper notes the series converges absolutely (p.14); stating summability rules out the junk value of a divergent series
--   - encoding: Algorithm 1 and "never returns fail" → `greedyRun` returning an `Option` (`none` = fail), and `∀ b, greedyRun … b ≠ none`; reason: a direct transcription of the pseudocode, with the threshold recursion terminating as in the paper
--   - encoding: $\varphi^\alpha_S$ weakly increasing in $s$ → monotone on $\{0,\dots,K\}$, the positive-mass points; reason: the paper defines $\varphi^\alpha_S$ on positive-mass points
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Theorem 4.10, p.15

import Mathlib
import Definitions.Def_SecondBestBT_IsFullSupportOn
import Definitions.Def_SecondBestBT_IsAlphaWeaklyRegular
import Definitions.Def_SecondBestBT_greedyAlloc
import Definitions.Def_SecondBestBT_R3N
import Definitions.Def_SecondBestBT_gftTermN
import Definitions.Def_SecondBestBT_lambdaTermN
import Definitions.Def_SecondBestBT_fbTermN

namespace SecondBestBT

/-- **Theorem 4.10** (guarantee of the greedy construction; Liu–Qin–Ren–Wang, *Second-Best
Bilateral Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…,
Theorem 4.10, p.15). Fix `α, β ≥ 0` and an `α`-weakly regular seller prior `F_S` with full
support on `{0, 1, …, K}`. If Algorithm 1 never returns fail, the allocation rule `x` it defines
satisfies `x ∈ R3` and `H(b; x) ≥ 0` for every `b ∈ ℤ_{≥0}`. Consequently, for every buyer prior
`F_B` on `ℤ_{≥0}` with finite first-best GFT, `GFT(x) + α Λ_D(x) − β FB ≥ 0`, which gives
`sup_{x ∈ R3} inf_{F_B} [GFT(x) + α Λ_D(x) − β FB] ≥ 0`.

**Formalization Note** The consequence is stated for the algorithm's output, which implies the
printed `sup–inf` form. For a buyer prior with infinite support, `GFT`, `Λ_D` and `FB` are series
over `(s, b) ∈ ℕ × ℕ`; the conclusion asserts that the `GFT` and `Λ_D` series are summable (so
neither is a junk value) and that the combination is nonnegative. -/
theorem theorem_4_10 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (K : ℕ) (fS : ℕ → ℝ)
    (hfS : IsFullSupportOn fS K) (hreg : IsAlphaWeaklyRegular α fS K)
    (hnf : ∀ b, greedyRun α β K fS b ≠ none) :
    greedyAlloc α β K fS ∈ R3N ∧ (∀ b, 0 ≤ H α β fS (greedyAlloc α β K fS) b) ∧
    ∀ fB : ℕ → ℝ, (∀ b, 0 ≤ fB b) → HasSum fB 1 → Summable (fbTermN fS fB) →
      Summable (gftTermN fS fB (greedyAlloc α β K fS)) ∧
      Summable (lambdaTermN fS fB (greedyAlloc α β K fS)) ∧
      0 ≤ (∑' p, gftTermN fS fB (greedyAlloc α β K fS) p) +
          α * (∑' p, lambdaTermN fS fB (greedyAlloc α β K fS) p) -
          β * ∑' p, fbTermN fS fB p := by sorry

end SecondBestBT
