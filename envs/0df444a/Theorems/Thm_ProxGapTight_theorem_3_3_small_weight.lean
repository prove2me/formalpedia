-- Prove2me | Theorems.Thm_ProxGapTight_theorem_3_3_small_weight
-- name    : ProxGapTight.theorem_3_3_small_weight
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:57:14.148451+00:00
-- url     : https://prove2.me/theorems/e4fba41c-9ad8-4c68-95bc-7b1a1de53b56
-- title:
--   Theorem 3.3 ([AD21]) — words of $U_m$ of weight $\le L_m$ are combinations of at most two $u_W$
-- statement:
--   Let $p$ be a prime and $Q=p^a$ with $Q>32$ and $Q\notin\{49,121\}$. There is $m_0$ such that for every $m\ge m_0$: every word $v\in U_m\subseteq\mathbb F_p^X$ with $\mathrm{wt}(v)\le L_m=3Q^{m-3}-3Q^{m-4}-1$ is an $\mathbb F_p$-linear combination of at most two incidence vectors,
--   $$
--   v=\alpha u_W+\beta u_{W'},\qquad W,W'\in\mathrm{Gr}(m-2,\mathbb F_Q^m),\ \alpha,\beta\in\mathbb F_p.
--   $$
--
--   This is a result of Adriaensen and Denaux on the codes of points and $k$-spaces of projective spaces [AD21, Theorem 5.9], translated to the paper's notation. It is the structural input from which the shortening properties of $U_m$ (Lemma 3.4) follow.
--
--   **Formalization Note** $\mathbb F_Q$ is any field of order $p^a$; $m_0$ depends only on $p$ and $a$.
--
--   Differences from the source:
--   - reading: Theorem 3.3 has no explicit range of m; p.7 fixes 'p, Q, m as in the lemma' (Lemma 3.2: for all sufficiently large m) → ∃ m₀ (depending on p, a) such that the statement holds for all m ≥ m₀; reason: this is the claim the paper makes in context; it does not claim the statement for every m
--   - generalization: F_Q → any field with Fintype.card = p ^ a; reason: all fields of that order are isomorphic to it; the statement specializes to it
--   - encoding: an F_p-linear combination of at most two incidence vectors u_W → α • u_W + β • u_{W'} with W = W' and zero coefficients allowed; reason: the same set of words
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Theorem 3.3, p.8 (context: Lemma 3.2 and 'Fix p, Q, m as in the lemma', p.7)

import Mathlib
import Definitions.Def_ProxGapTight_Um
import Definitions.Def_ProxGapTight_Lm

namespace ProxGapTight

/-- **Theorem 3.3** ([AD21]), Kominers, Thaler, Zheng, manuscript (Sept. 2026), p.8: "Every word of
`U_m` of weight at most `L_m` is an `F_p`-linear combination of at most two incidence vectors `u_W`."
The theorem is cited from Adriaensen–Denaux [AD21, Theorem 5.9]; the paper's proof is a translation
of notation.

**Formalization Note.** The standing context is "Fix p, Q, m as in the lemma" (p.7, Lemma 3.2):
`p` prime, `Q = p^a > 32`, `Q ∉ {49, 121}`, `m` sufficiently large; this is the `∃ m₀` (depending
on `p, a` only). `F_Q` is any field `K` of order `p^a`. "At most two" is `α • u_W + β • u_{W'}`
with `W = W'` and zero coefficients allowed. -/
theorem theorem_3_3_small_weight (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p ^ a →
      ∀ v ∈ Um K m p, hammingNorm v ≤ Lm (p ^ a) m →
        ∃ W W' : Codim2 K m, ∃ α β : ZMod p,
          v = α • incVec (ZMod p) W + β • incVec (ZMod p) W' := by sorry

end ProxGapTight
