-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_corollary_3_5
-- name    : RSListDecodingCapacity.AllRates.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:53.505677+00:00
-- url     : https://prove2.me/theorems/3278d682-a106-44f8-97ca-954ec07e67d6
-- title:
--   Corollary 3.5 — volume of the scaled simplex $S_z$
-- statement:
--   Let $d\ge1$ and $z\in\mathbb R_{\ge0}$. The scaled simplex
--   $$S_z=\Big\{x\in\mathbb R_{\ge0}^{d-1}:\sum_{i=1}^{d-1}i\cdot x_i\le z\Big\}$$
--   has $(d-1)$-dimensional Lebesgue volume
--   $$\mathrm{Vol}(S_z)=\frac{z^{d-1}}{((d-1)!)^2}.$$
--
--   It converts volume estimates into the lattice-count estimates of Corollary 3.8 and Lemma 3.3. The case $z=0$ is included (the volume is $0$ for $d\ge2$).
--
--   Differences from the source:
--   - generalization: d the §3 parameter (d ≥ 2) → every d ≥ 1, including d = 1 (ℝ⁰, volume 1 = z⁰); reason: the d = 1 instance is the zero-dimensional case of the same formula; every source instance is covered
--   - encoding: Vol(S_z) as a real number → MeasureTheory.volume (an extended nonnegative real) = ENNReal.ofReal(z^(d−1)/((d−1)!)²); reason: Lean's Lebesgue measure takes values in [0, ∞]; the equation also asserts finiteness
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.18, Corollary 3.5

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Simplices

namespace RSListDecodingCapacity.AllRates

/-- **Corollary 3.5** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.18).
For `z ≥ 0`, the scaled simplex `S_z = {x ∈ ℝ_{≥0}^{d−1} : ∑ᵢ i · xᵢ ≤ z}` has
`(d − 1)`-dimensional volume `z^{d−1} / ((d − 1)!)²`. -/
theorem corollary_3_5 (d : ℕ) (hd : 1 ≤ d) (z : ℝ) (hz : 0 ≤ z) :
    MeasureTheory.volume (simplexS d z) =
      ENNReal.ofReal (z ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) := by sorry

end RSListDecodingCapacity.AllRates
