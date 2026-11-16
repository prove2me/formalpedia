-- Prove2me | Theorems.Thm_PlantedIQP_Supplement_theorem_53
-- name    : PlantedIQP.Supplement.theorem_53
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:05:37.826355+00:00
-- url     : https://prove2.me/theorems/f66ae8a7-b3a2-46c5-9414-b8d353b87477
-- title:
--   Theorem 53 — $\mathrm{SR}(P)\le r$ iff an independent triple of spaces of dimension $\ge \ell+m+n-r$
-- statement:
--   **Theorem 53.** Let $F$ be any field and let $P(x,y,z)=\sum_{a\le\ell,\,b\le m,\,c\le n}p_{abc}x_ay_bz_c$ be a trilinear form in $\ell+m+n$ variables. For every $r\in\mathbb N$,
--
--   $$
--   \mathrm{SR}(P)\le r\iff \exists\,V_x\le F^\ell,\ V_y\le F^m,\ V_z\le F^n:\ P(V_x,V_y,V_z)=\{0\}\ \text{and}\ \dim V_x+\dim V_y+\dim V_z\ge \ell+m+n-r .
--   $$
--
--   Here $\mathrm{SR}(P)\le r$ means that $P$ has a slice decomposition $\sum_i\ell_{x,i}(x)B_{x,i}(y,z)+\sum_j\ell_{y,j}(y)B_{y,j}(x,z)+\sum_k\ell_{z,k}(z)B_{z,k}(x,y)$ with $r_x+r_y+r_z\le r$ terms (Definition 49). $P(V_x,V_y,V_z)=\{0\}$ means that $P$ vanishes on $V_x\times V_y\times V_z$ (Definition 51).
--
--   The theorem turns slice rank into a statement about large subspaces on which the form vanishes. This is the trilinear model for the correspondence between symmetric slice rank and independent spaces of cubic forms (Theorem 60).
--
--   **Formalization Note** $P$ is its coefficient tensor and is not assumed symmetric. $\ell,m,n$ may be $0$.
--
--   Differences from the source:
--   - encoding: dimension ≥ ℓ + m + n − r (an integer) → ℓ + m + n − r in ℕ (truncated); reason: dimensions are nonnegative, so the two readings agree for every r
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Theorem 53, p.29 (Definitions 49 and 51, p.29)

import Mathlib
import Definitions.Def_PlantedIQP_Supplement_SliceRank

set_option autoImplicit false

namespace PlantedIQP.Supplement

/-- **Theorem 53** (Bläser, Gullans, Hangleiter, Liu, Qiao, arXiv:2609.39918, sha256 6e261694…,
Theorem 53, p.29). "For any trilinear form P, SR(P) ≤ r iff there is an independent triple of
spaces of dimension ≥ ℓ + m + n − r."

**Formalization Note.** Over every field `F` (Section 4, p.28), for every `ℓ, m, n` (including `0`)
and every `r : ℕ`. `P` is its coefficient tensor `p` (not assumed symmetric or alternating);
`SR(P) ≤ r` is `SliceRankLE p r` and the triple is `IsIndependentTriple`. The bound
`ℓ + m + n − r` is natural-number subtraction: when `r ≥ ℓ + m + n` it is `0`, which agrees with
the integer reading because dimensions are nonnegative. -/
theorem theorem_53 {F : Type*} [Field F] {ℓ m n : ℕ} (p : TriTensor F ℓ m n) (r : ℕ) :
    SliceRankLE p r ↔
      ∃ (Vx : Submodule F (Fin ℓ → F)) (Vy : Submodule F (Fin m → F))
        (Vz : Submodule F (Fin n → F)),
        IsIndependentTriple p Vx Vy Vz ∧
          ℓ + m + n - r ≤ Module.finrank F Vx + Module.finrank F Vy + Module.finrank F Vz := by sorry

end PlantedIQP.Supplement
