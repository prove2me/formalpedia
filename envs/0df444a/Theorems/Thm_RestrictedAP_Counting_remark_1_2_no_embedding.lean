-- Prove2me | Theorems.Thm_RestrictedAP_Counting_remark_1_2_no_embedding
-- name    : RestrictedAP.Counting.remark_1_2_no_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:17.154222+00:00
-- url     : https://prove2.me/theorems/4a5af932-c5e7-401f-887b-eace802b51c1
-- title:
--   §1.2 remark — the somewhat restricted 3-AP distribution $\mu_p$ has no $(\mathbb Z,+)$-embedding
-- statement:
--   Let $p\ge3$ be prime and let $\mu_p$ be the law of $(x,x+a,x+2a)\in\mathbb F_p^3$ for independent uniform $x\in\mathbb F_p$ and $a\in\{0,1,2\}$. Then $\mu_p$ has no $(\mathbb Z,+)$-embedding: there are no maps $\sigma,\gamma,\phi:\mathbb F_p\to\mathbb Z$, not all constant, with
--   $$\sigma(x)+\gamma(x+a)+\phi(x+2a)=0\qquad\text{for all }x\in\mathbb F_p,\ a\in\{0,1,2\}.$$
--
--   The paper calls this "a routine exercise" (§1.2, citing [BKM24a]); together with Theorem 1.4 it gives Theorem 1.2, since $\mu_p$ has uniform marginals, contains the diagonal ($a=0$), has all atoms of probability $1/(3p)$, and $\mu_p^{\otimes n}$ is the law of the triple in Theorem 1.2.
--
--   Differences from the source:
--   - reading: 'somewhat restricted 3-APs do not admit (Z,+)-embeddings' → the distribution μ_p (a uniform on {0, 1, 2}, a = 0 included) has no (ℤ,+)-embedding; reason: the distribution to which Theorem 1.4 is applied to obtain Theorem 1.2
--   - encoding: μ_p as a law → weight #{(x, a) : (x, x + a, x + 2a) = t}/(3p) (`muP p`); reason: uniform (x, a); only the support enters the statement
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, §1.2, remark before Theorem 1.4

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_MuP

namespace RestrictedAP.Counting

/-- **§1.2, remark before Theorem 1.4** (p. 3). For every prime `p ≥ 3`, the somewhat
restricted 3-AP distribution `μ_p` (the law of `(x, x + a, x + 2a)`, `x` uniform on `F_p`,
`a` uniform on `{0,1,2}`) has no `(ℤ,+)`-embedding: there are no maps
`σ, γ, φ : F_p → ℤ`, not all constant, with `σ(x) + γ(y) + φ(z) = 0` on `supp(μ_p)`. -/
theorem remark_1_2_no_embedding (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ¬ DistHasEmbedding ℤ (muP p) := by sorry

end RestrictedAP.Counting
