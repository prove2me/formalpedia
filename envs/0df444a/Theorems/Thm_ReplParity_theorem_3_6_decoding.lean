-- Prove2me | Theorems.Thm_ReplParity_theorem_3_6_decoding
-- name    : ReplParity.theorem_3_6_decoding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:51.051312+00:00
-- url     : https://prove2.me/theorems/1da24d60-5ff5-4817-a77b-84d4ff5d00e8
-- title:
--   Proof of Theorem 3.6, p.19 — decoding a covering subspace into a parity
-- statement:
--   Let $Z$ be a subspace of $\mathbb F_2^{d+1}$.
--
--   1. If $Z\subseteq G_{z^\star}$ for some $z^\star$, then $e_{d+1}\notin Z$.
--   2. If $e_{d+1}\notin Z$, the linear system $\langle z,x\rangle=y$ for $(x,y)\in Z$ is consistent: $Z\subseteq G_z$ for some $z$.
--   3. For every labeled distribution $D$ on $\mathbb F_2^d\times\{0,1\}$ and every $z$ with $Z\subseteq G_z$,
--   $$\mathrm{err}_D(f_z)\le Q(\mathbb F_2^{d+1}\setminus Z),$$
--   where $Q$ is the law of the lifted example $(x,y)$ under $D$.
--
--   These are the deterministic steps by which the proof of Theorem 3.6 turns the subspace $Z$ of Proposition 3.5 into a parity.
--
--   Differences from the source:
--   - reading: the learner solves ⟨z, x⟩ = y over a canonical basis of Z, sets the free variables to zero, and the output parity agrees with every vector of Z → (2) some z with Z ⊆ G_z exists, and (3) holds for every such z; reason: the error bound uses only that f_z agrees with Z; the canonical solution is one such z, and its determinism matters only for replicability, which the goal carries
--   - reading: …, which is at most ε except with probability δ → not part of this item; it is the coverage clause of ReplParity.proposition_3_5, used in ReplParity.theorem_3_6; reason: this item is the deterministic decoding step; the probabilistic step is Proposition 3.5's statement
--   - encoding: Q, the law of the lifted examples → D.map lift; reason: the push-forward of D under (x, y) ↦ (x, y) ∈ 𝔽ᵈ⁺¹₂
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Theorem 3.6, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ReplParity_parity
import Definitions.Def_ReplParity_err
import Definitions.Def_ReplParity_massOutside

namespace ReplParity

/-- **Decoding a covering subspace into a parity (proof of Theorem 3.6).** Shen, Zhong, *Replicable
Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission
(manuscript sha256 40424491…), proof of Theorem 3.6, p.19 (PDF p.21): "Suppose that D is realized by
f_{z⋆}. Every lifted sample vector lies in G_{z⋆}, so containment gives Z ⊆ G_{z⋆}, and in particular
e_{d+1} ∉ Z and the system is consistent. The output parity agrees with every vector of Z, so
err_D(f_z) ≤ Q(𝔽ᵈ⁺¹₂ \ Z)".

For every subspace `Z` of `𝔽ᵈ⁺¹₂`:
(a) if `Z ⊆ G_{z⋆}` then `e_{d+1} ∉ Z`;
(b) if `e_{d+1} ∉ Z`, the system `⟨z, x⟩ = y` for `(x, y) ∈ Z` has a solution, i.e. `Z ⊆ G_z` for
some `z`;
(c) for every labeled distribution `D` and every `z` with `Z ⊆ G_z`,
`err_D(f_z) ≤ Q(𝔽ᵈ⁺¹₂ \ Z)`, where `Q` is the law of the lifted example under `D`. -/
theorem theorem_3_6_decoding (d : ℕ) (Z : Subsp (d + 1)) :
    (∀ zs : Vec d, Z ≤ hyperplaneG zs → eLast d ∉ Z) ∧
    (eLast d ∉ Z → ∃ z : Vec d, Z ≤ hyperplaneG z) ∧
    (∀ (D : PMF (Example d)) (z : Vec d), Z ≤ hyperplaneG z →
      err D (parity z) ≤ massOutside (D.map lift) Z) := by sorry

end ReplParity
