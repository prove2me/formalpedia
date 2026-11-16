-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_lemma_C_8
-- name    : SFMQueryLower.EmptyMin.Supplement.lemma_C_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:30:44.810522+00:00
-- url     : https://prove2.me/theorems/9bf5bd35-7839-42fa-bc80-9003069e51c0
-- title:
--   Lemma C.8 — three prefix queries answer one value query to $\tilde h_{z,\sigma}$, without knowing $z$ or $\sigma$
-- statement:
--   Let $k\ge2$, and for a $\mathrm{HiddenPermutation}_k$ instance $(z,\sigma)$ let $\tilde h_{z,\sigma}=h_k^{\pi_{z,\sigma}}$ be the CGJS function of Definition C.7.
--
--   For every $S\subseteq[2k]$ there is a deterministic prefix-query procedure $B_S$, fixed before $(z,\sigma)$, such that for every instance $(z,\sigma)$, run on the oracle $\operatorname{prefix-len}_{z,\sigma}$, it makes at most three prefix queries and returns
--   $$\tilde h_{z,\sigma}(S).$$
--
--   This lets an algorithm for the CGJS family run on a hidden-permutation instance, which is the reduction behind the lower bound of Theorem C.9.
--
--   **Formalization Note** Procedures are the published deterministic `OracleStrategy`; queries may be adaptive. The query count includes every issued query.
--
--   Differences from the source:
--   - encoding: "for any $S$ we can compute $\tilde h_{z,\sigma}(S)$ using three queries to $\operatorname{prefix-len}_{z,\sigma}$ without knowing $z$ or $\sigma$" → for each $S$ there exists a deterministic strategy, quantified before $(z,\sigma)$, that returns the value on every instance with at most three issued queries; reason: quantifying the procedure before the instance is the meaning of "without knowing $z$ or $\sigma$", and a procedure can always repeat a query to use exactly three.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma C.8, printed p. 23 / PDF p. 24 (proof printed pp. 23–24 / PDF pp. 24–25)

import Definitions.Def_SFMQueryLower_EmptyMin_OracleStrategy
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSEncoding

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Lemma C.8, printed p. 23 / PDF p. 24 (proof pp. 23–24 / PDF pp. 24–25).
For every `S ⊆ [2k]` a deterministic prefix-query procedure `B`, fixed before the hidden
instance `(z, σ)` ("without knowing z or σ"), returns `h̃_{z,σ}(S)` exactly, using at most three
prefix queries. Adaptive queries are allowed. -/
theorem lemma_C_8 (k : ℕ) (hk : 2 ≤ k) (S : Finset (Fin (2 * k))) :
    ∃ B : OracleStrategy (Fin k → Bool) ℕ ℝ,
      ∀ (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)),
        Returns B (prefixLen z σ) (encodedFunction z σ S) ∧
        queryCount B (prefixLen z σ) (fun _ => True) ≤ 3 := by sorry

end SFMQueryLower.EmptyMin.Supplement
