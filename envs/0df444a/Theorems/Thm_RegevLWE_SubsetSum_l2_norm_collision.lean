-- Prove2me | Theorems.Thm_RegevLWE_SubsetSum_l2_norm_collision
-- name    : RegevLWE.SubsetSum.l2_norm_collision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:37.039554+00:00
-- url     : https://prove2.me/theorems/d3b121e2-7327-4d10-85a0-968a3e5d2f79
-- title:
--   Proof of Claim 5.3, p. 34:36 — Σ_h P_g(h)² = Pr_{b,b′}[Σb_ig_i = Σb′_ig_i] ≤ 1/2^l + Pr[· | b ≠ b′]
-- statement:
--   Let $G$ be a finite abelian group, $l \ge 0$, and $g = (g_1, \dots, g_l) \in G^l$. Let $P_g(h) = 2^{-l}|\{b \in \{0,1\}^l \mid \sum_i b_i g_i = h\}|$ be the distribution of the sum of a uniformly random subset of $g_1, \dots, g_l$, and let $b, b'$ be independent and uniform in $\{0,1\}^l$. Then the $\ell_2$ norm of $P_g$ is the collision probability of the two subset sums, and is bounded by the probability that $b = b'$ plus the conditional collision probability given $b \neq b'$:
--   $$\sum_{h \in G} P_g(h)^2 = \Pr_{b,b'}\Bigl[\sum_i b_i g_i = \sum_i b'_i g_i\Bigr] \le \frac{1}{2^l} + \Pr_{b,b'}\Bigl[\sum_i b_i g_i = \sum_i b'_i g_i \Bigm| b \neq b'\Bigr].$$
--
--   This is the first step of the proof of Claim 5.3: it turns the $\ell_2$ norm of $P_g$ into a count over pairs of subsets, which can then be averaged over $g$.
--
--   **Formalization Note** The probabilities are counts over the $(2^l)^2$ pairs $(b, b')$: the unconditional probability divides the number of colliding pairs by $(2^l)^2$, and the conditional one divides the number of colliding pairs with $b \neq b'$ by the number $(2^l)^2 - 2^l$ of pairs with $b \neq b'$. For $l = 0$ there is no pair with $b \neq b'$; the conditional probability is then undefined in the paper and Lean's division gives $0/0 = 0$, and the inequality reads $1 \le 1 + 0$, which holds.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:36, proof of Claim 5.3, last display

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic

open Finset

namespace RegevLWE.SubsetSum

/-- Proof of Claim 5.3 (Regev, J. ACM 2009, p. 34:36, last display): the `ℓ₂` norm of `P_g` is the
collision probability of two independent uniform `b, b' ∈ {0,1}^l`,
`∑_h P_g(h)² = Pr_{b,b'}[∑ bᵢgᵢ = ∑ b'ᵢgᵢ] ≤ 1/2^l + Pr_{b,b'}[∑ bᵢgᵢ = ∑ b'ᵢgᵢ | b ≠ b']`.
Probabilities over `(b, b')` are counts over the `(2^l)²` pairs; the conditional probability is the
count of colliding pairs with `b ≠ b'` divided by the number `(2^l)² − 2^l` of pairs with `b ≠ b'`. -/
theorem l2_norm_collision {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (g : Fin l → G) :
    ∑ h, P g h ^ 2 =
        ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) / ((2 : ℝ) ^ l) ^ 2 ∧
      ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
            subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) / ((2 : ℝ) ^ l) ^ 2 ≤
        1 / (2 : ℝ) ^ l +
          ((univ.filter fun bb : (Fin l → Bool) × (Fin l → Bool) =>
              bb.1 ≠ bb.2 ∧ subsetSum g bb.1 = subsetSum g bb.2).card : ℝ) /
            (((2 : ℝ) ^ l) ^ 2 - (2 : ℝ) ^ l) := by sorry

end RegevLWE.SubsetSum
