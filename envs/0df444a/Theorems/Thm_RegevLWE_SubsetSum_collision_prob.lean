-- Prove2me | Theorems.Thm_RegevLWE_SubsetSum_collision_prob
-- name    : RegevLWE.SubsetSum.collision_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:33.961214+00:00
-- url     : https://prove2.me/theorems/c75c3ab4-cd2f-4859-bf34-7a0dd1c681b2
-- title:
--   Proof of Claim 5.3, p. 34:37 — for b ≠ b′, Pr_g[Σ b_ig_i = Σ b′_ig_i] = 1/|G|
-- statement:
--   Let $G$ be a finite abelian group and $l \ge 0$. For any two distinct vectors $b \neq b'$ in $\{0,1\}^l$, over a uniform choice of $g = (g_1, \dots, g_l) \in G^l$,
--   $$\Pr_g\Bigl[\sum_i b_i g_i = \sum_i b'_i g_i\Bigr] = \frac{1}{|G|}.$$
--
--   This fact is what makes the expected $\ell_2$ norm of $P_g$ small: two different subsets of uniformly random group elements have equal sums only with probability $1/|G|$.
--
--   **Formalization Note** The probability is the number of tuples $g \in G^l$ with $\sum_i b_i g_i = \sum_i b'_i g_i$ divided by $|G|^l$. The hypothesis $b \neq b'$ forces $l \ge 1$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:37, proof of Claim 5.3, first sentence

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic

open Finset

namespace RegevLWE.SubsetSum

/-- Proof of Claim 5.3 (Regev, J. ACM 2009, p. 34:37, first sentence): for any `b ≠ b'` in
`{0,1}^l`, over a uniform choice of `g = (g₁, …, g_l) ∈ G^l`,
`Pr_g[∑ bᵢgᵢ = ∑ b'ᵢgᵢ] = 1/|G|`. The probability is the number of tuples `g` with
`∑ bᵢgᵢ = ∑ b'ᵢgᵢ` divided by `|G|^l`. -/
theorem collision_prob {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (b b' : Fin l → Bool) (hb : b ≠ b') :
    ((univ.filter fun g : Fin l → G => subsetSum g b = subsetSum g b').card : ℝ) /
        (Fintype.card G : ℝ) ^ l = 1 / (Fintype.card G : ℝ) := by sorry

end RegevLWE.SubsetSum
