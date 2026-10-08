-- Prove2me | Theorems.Thm_RegevLWE_SubsetSum_claim_5_3
-- name    : RegevLWE.SubsetSum.claim_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:44.250496+00:00
-- url     : https://prove2.me/theorems/f329af65-b825-4695-8504-66179acf49b3
-- title:
--   Claim 5.3, p. 34:36 — a random subset sum of l uniform elements of G is on average within √(|G|/2^l) of uniform
-- statement:
--   Let $G$ be a finite abelian group and $l \ge 0$ an integer. For $g = (g_1, \dots, g_l) \in G^l$ let
--   $$P_g(h) = \frac{1}{2^l}\,\bigl|\{\, b \in \{0,1\}^l \mid \textstyle\sum_i b_i g_i = h \,\}\bigr|$$
--   be the distribution of the sum of a uniformly random subset of $g_1, \dots, g_l$, and let
--   $\Delta(g) = \sum_{h \in G} |P_g(h) - 1/|G||$ be its statistical distance from the uniform distribution on $G$. Choose $g_1, \dots, g_l \in G$ uniformly and independently. Then
--
--   1. the expected statistical distance is at most $\sqrt{|G|/2^l}$:
--   $$\mathop{\mathrm{Exp}}_g\bigl[\Delta(g)\bigr] \le \sqrt{\frac{|G|}{2^l}};$$
--   2. the probability that the statistical distance is more than $\sqrt[4]{|G|/2^l}$ is at most $\sqrt[4]{|G|/2^l}$:
--   $$\Pr_g\Bigl[\Delta(g) > \sqrt[4]{|G|/2^l}\Bigr] \le \sqrt[4]{\frac{|G|}{2^l}}.$$
--
--   This is the special case of the leftover hash lemma of Impagliazzo and Zuckerman (1989) that Regev uses to prove the semantic security of his LWE-based public-key cryptosystem: once $2^l$ is much larger than $|G|$, a random subset sum of a random public key is close to uniform for almost every key.
--
--   **Formalization Note** $\mathrm{Exp}_g$ and $\Pr_g$ are exact averages over all $|G|^l$ tuples $g$ (the probability is the number of tuples with $\Delta(g) > \sqrt[4]{|G|/2^l}$ divided by $|G|^l$). The statistical distance has no factor $\tfrac12$. The fourth root is written `Real.sqrt (Real.sqrt x)`. No hypothesis is added: $|G| \ge 1$ holds for every group, and $l = 0$ is allowed.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:36, Claim 5.3

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic

open Finset

namespace RegevLWE.SubsetSum

/-- Claim 5.3 (Regev, J. ACM 2009, p. 34:36). Let `G` be a finite abelian group and `l ≥ 0`. For
`g = (g₁, …, g_l) ∈ G^l` let `P_g` be the distribution of the sum of a uniformly random subset of
`g₁, …, g_l`, and `Δ(g) = ∑_h |P_g(h) − 1/|G||` its statistical distance from uniform. Over a uniform
choice of `g ∈ G^l`:
1. `Exp_g[Δ(g)] ≤ √(|G|/2^l)`;
2. `Pr_g[Δ(g) > ⁴√(|G|/2^l)] ≤ ⁴√(|G|/2^l)`,
with the fourth root written `√(√·)`. -/
theorem claim_5_3 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (l : ℕ) :
    expectG (fun g : Fin l → G => statDistUniform g) ≤
        Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l) ∧
      ((univ.filter fun g : Fin l → G =>
            Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) < statDistUniform g).card : ℝ) /
          (Fintype.card G : ℝ) ^ l ≤
        Real.sqrt (Real.sqrt ((Fintype.card G : ℝ) / 2 ^ l)) := by sorry

end RegevLWE.SubsetSum
