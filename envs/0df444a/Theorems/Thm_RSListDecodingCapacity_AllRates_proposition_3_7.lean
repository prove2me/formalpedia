-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_proposition_3_7
-- name    : RSListDecodingCapacity.AllRates.proposition_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:41.355804+00:00
-- url     : https://prove2.me/theorems/68017378-9e4b-4465-a204-dabb5101422e
-- title:
--   Proposition 3.7 — the simplex is sandwiched by lattice cubes
-- statement:
--   Let $d\ge1$ and let $z$ be an integer. Then
--   $$S_z\ \subseteq\ \bigcup_{u\in\mathbb Z_{\ge0}^{d-1}:\ \sum_i i\,u_i\le z}\big(u+[0,1)^{d-1}\big)\ \subseteq\ S_{z+d(d-1)/2}.$$
--
--   With the exact volume of the cube union (Proposition 3.6) and of $S_z$ (Corollary 3.5) this yields both bounds of Corollary 3.8 on $\Lambda(z)$.
--
--   Differences from the source:
--   - generalization: d the §3 parameter (d ≥ 2) → every d ≥ 1; reason: the d = 1 instance is the trivial zero-dimensional case; every source instance is covered
--   - generalization: the scaled-simplex setting introduces z ≥ 0 before restricting z to integers → every integer z, including negative z; reason: for z < 0 the first simplex and the lattice-cube union are empty, so both containments still hold; all nonnegative source instances are retained
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.19, Proposition 3.7

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Simplices

namespace RSListDecodingCapacity.AllRates

/-- **Proposition 3.7** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.19).
For an integer `z`,
`S_z ⊆ ⋃_{∑ᵢ i uᵢ ≤ z} (u + [0, 1)^{d−1}) ⊆ S_{z + d(d−1)/2}`. -/
theorem proposition_3_7 (d : ℕ) (hd : 1 ≤ d) (z : ℤ) :
    simplexS d z ⊆ latticeCubeUnion d z ∧
      latticeCubeUnion d z ⊆ simplexS d ((z : ℝ) + (d : ℝ) * ((d : ℝ) - 1) / 2) := by sorry

end RSListDecodingCapacity.AllRates
