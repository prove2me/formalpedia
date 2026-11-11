-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_lemma_3_3
-- name    : ShuffleDecoys.Hierarchy.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:22:14.04661+00:00
-- url     : https://prove2.me/theorems/2581037d-b353-4f73-b645-7fbc1dd93d01
-- title:
--   Lemma 3.3 — the sine-squared law and its unit shift: Σ √(r(j) r₊(j)) = cos θ and ‖√r − √r₊‖²₂ = 2 − 2 cos θ
-- statement:
--   Fix $d\ge2$, $n\ge d$, and let $r$ be the sine-squared distribution of construction (8), $r(j)=\frac{2}{L+1}\sin^2((j+1)\theta)$ for $j=0,\dots,L-1$ with $L=\lfloor(n-1)/(d-1)\rfloor+1$, $\theta=\pi/(L+1)$, extended by zero outside $\{0,\dots,L-1\}$. With $r_+(j)=r(j-1)$,
--   $$\sum_{j\in\mathbb Z}\sqrt{r(j)\,r_+(j)}=\cos\theta,\qquad \big\|\sqrt r-\sqrt{r_+}\big\|_2^2=2-2\cos\theta.$$
--
--   Differences from the source:
--   - encoding: sums over $j\in\mathbb Z$ → `tsum` over `ℤ` of the finitely supported terms; reason: the series has finitely many nonzero terms.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 17, Lemma 3.3, Eq. (9)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_SineNoise

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Lemma 3.3: for `d ≥ 2`, `n ≥ d`, the sine-squared law `r` of construction (8) (zero
outside `{0, …, L − 1}`) and its unit shift `r₊(j) = r(j − 1)` satisfy
`Σ_{j∈ℤ} √(r(j) r₊(j)) = cos θ` and `‖√r − √r₊‖₂² = 2 − 2 cos θ`. -/
theorem lemma_3_3 (d n : ℕ) (hd : 2 ≤ d) (hn : d ≤ n) :
    (∑' j : ℤ, Real.sqrt (sineWeight d n j * sineWeight d n (j - 1)) =
        Real.cos (sineTheta d n)) ∧
    (∑' j : ℤ, (Real.sqrt (sineWeight d n j) - Real.sqrt (sineWeight d n (j - 1))) ^ 2 =
        2 - 2 * Real.cos (sineTheta d n)) := by sorry

end ShuffleDecoys.Hierarchy
