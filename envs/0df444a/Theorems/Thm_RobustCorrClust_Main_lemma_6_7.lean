-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_6_7
-- name    : RobustCorrClust.Main.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:39:23.578125+00:00
-- url     : https://prove2.me/theorems/0f346a0a-c339-4a8c-8be0-0cc3b3afca0d
-- title:
--   Lemma 6.7 — triangular-threshold inequality (13)
-- statement:
--   Let $\theta=(U_1+U_2)/2$ with $U_1,U_2$ independent uniform random variables on $[0,1]$. For every real $\hat y$, every $a,o\in\{0,1\}$ and every $\beta\ge1$,
--   $$\beta\Pr_\theta\big[\mathbf 1[\hat y\ge\theta]\ne o\big]+\Pr_\theta\big[\mathbf 1[\hat y\ge\theta]\ne a\big]\le(\beta+1)\big[(\hat y-a)^2+(\hat y-o)^2\big]+\frac{(\beta-1)^2}{4\beta}\mathbf 1[a\ne o].$$
--   In the paper $\hat y=\hat Y_{uv}$, $a=A_{uv}$ and $o=O^{\mathcal C^*}_{uv}$ for a pair $u<v$; the inequality charges the rounding mistakes of the pair to its squared SDP errors.
--
--   Differences from the source:
--   - generalization: $\hat Y_{uv}$, $A_{uv}$, $O^{\mathcal C^*}_{uv}$ for a pair $u<v$ → any real $\hat y$ and any $a,o\in\{0,1\}$; reason: the pair's three values are such numbers and the inequality is pointwise in them.
--   - encoding: $\Pr_\theta$ → the Lebesgue measure of the corresponding subset of $[0,1]^2$; reason: the law of $(U_1,U_2)$.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 50, Lemma 6.7

import Mathlib
import Definitions.Def_RobustCorrClust_Main_Threshold

namespace RobustCorrClust.Main

/-- Lemma 6.7 (p. 50), eq. (13), for every real value `ŷ` (the pair's `Ŷ_uv`) and binary values
`a, o ∈ {0, 1}` (the pair's `A_uv` and `O^{C*}_uv`), and every `β ≥ 1`:
`β Pr_θ[1[ŷ ≥ θ] ≠ o] + Pr_θ[1[ŷ ≥ θ] ≠ a] ≤ (β+1)[(ŷ − a)² + (ŷ − o)²] + ((β−1)²/(4β)) 1[a ≠ o]`,
`θ = (U₁ + U₂)/2` with `U₁, U₂` independent uniform on `[0, 1]`. -/
theorem lemma_6_7 (yhat a o β : ℝ) (ha : a = 0 ∨ a = 1) (ho : o = 0 ∨ o = 1) (hβ : 1 ≤ β) :
    β * thrProb yhat o + thrProb yhat a ≤
      (β + 1) * ((yhat - a) ^ 2 + (yhat - o) ^ 2) +
        ((β - 1) ^ 2 / (4 * β)) * (if a ≠ o then 1 else 0) := by sorry

end RobustCorrClust.Main
