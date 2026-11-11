-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_theorem_3_4
-- name    : ShuffleDecoys.Hierarchy.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:45.79299+00:00
-- url     : https://prove2.me/theorems/d07da216-9b21-4a8d-a1e4-561fb2dcdcd9
-- title:
--   Theorem 3.4 — correlated sine-squared noise leaks I(M; T) ≤ 2d(d − 1)π²/(L + 1)² = O_d(n⁻²) for every prior on [d]
-- statement:
--   Fix $d\ge2$ and let $n\ge d$. For any prior $P$ on $[d]$, let $M\sim P$, generate $S$ according to construction (8) independently of $M$, and release $T=e_M+S$. Then
--   $$I(M;T)\ \le\ \frac{2d(d-1)\pi^2}{(L+1)^2}=O_d(n^{-2}),\qquad L=\Big\lfloor\frac{n-1}{d-1}\Big\rfloor+1,$$
--   uniformly over $P$ (priors with zero entries included). The $O_d(n^{-2})$ claim is stated with an explicit constant: there is $C>0$ (depending on $d$) with $2d(d-1)\pi^2/(L+1)^2\le C/n^2$ for all $n\ge d$.
--
--   Differences from the source:
--   - encoding: "$S$ generated according to (8), independently of $M$" → any law $S$ with `IsSineNoise d n S`, joint law `noiseJoint P S`; reason: `IsSineNoise` pins down the law of (8) uniquely.
--   - reading: $O_d(n^{-2})$ → $\exists C>0,\ \forall n\ge d$, bound $\le C/n^2$; reason: the standard reading with a constant depending on $d$ only, on the theorem's range $n\ge d$.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 18, Theorem 3.4, Eq. (10)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model
import Definitions.Def_ShuffleDecoys_Hierarchy_SineNoise

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Theorem 3.4: fix `d ≥ 2`; for every `n ≥ d`, every prior `P` on `[d]`, and `S` from
construction (8) independent of `M`, `T = e_M + S` leaks
`I(M; T) ≤ 2d(d − 1)π²/(L + 1)²`, `L = ⌊(n − 1)/(d − 1)⌋ + 1`; and this bound is `O_d(n⁻²)`. -/
theorem theorem_3_4 (d : ℕ) (hd : 2 ≤ d) :
    (∀ n : ℕ, d ≤ n → ∀ S : PMF (Fin d → ℤ), IsSineNoise d n S → ∀ P : PMF (Fin d),
      mutualInfo (noiseJoint P S) ≤
        ENNReal.ofReal (2 * (d : ℝ) * ((d : ℝ) - 1) * Real.pi ^ 2 /
          ((sineL d n : ℝ) + 1) ^ 2)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, d ≤ n →
      2 * (d : ℝ) * ((d : ℝ) - 1) * Real.pi ^ 2 / ((sineL d n : ℝ) + 1) ^ 2 ≤
        C / (n : ℝ) ^ 2) := by sorry

end ShuffleDecoys.Hierarchy
