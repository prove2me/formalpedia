-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_condEntropy_le_entropy
-- name    : WildeQIT.ZhangAudenaert.condEntropy_le_entropy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:17.68564+00:00
-- url     : https://prove2.me/theorems/f1ceacff-b34f-4d9e-bfd6-0c554d5ca11f
-- title:
--   Theorem 10.2.1 (Conditioning Does Not Increase Entropy): $H(X|Y)\le H(X)$, with equality iff independent
-- statement:
--   Let $X$ and $Y$ be random variables on finite alphabets $\mathcal X$ and $\mathcal Y$ with joint distribution $p_{X,Y}$, marginal $p_X$, entropy $H(X)$ and conditional entropy $H(X|Y)=-\sum_{x,y}p_{X,Y}(x,y)\log p_{X|Y}(x|y)$ (in bits). Then
--
--   $$
--   H(X)\ge H(X|Y),
--   $$
--
--   and equality holds if and only if $X$ and $Y$ are independent, that is, $p_{X,Y}(x,y)=p_X(x)\,p_Y(y)$ for all $x,y$.
--
--   Side information never increases uncertainty on average. The inequality is used in the proof of Fano's inequality (10.87), and it is equivalent to the non-negativity of mutual information.
--
--   **Formalization Note** The pair is represented by its joint distribution on a product of finite types; independence is `FinDist.Indep`.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.2.1, eq. (10.20), pp. 293–294

import Mathlib
import Definitions.Def_WildeQIT_entropy
import Definitions.Def_WildeQIT_condEntropy

namespace WildeQIT.ZhangAudenaert

/-- **Theorem 10.2.1 (Conditioning Does Not Increase Entropy).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.2.1, (10.20),
pp. 293–294: "The entropy `H(X)` is greater than or equal to the conditional entropy `H(X|Y)`:
`H(X) ≥ H(X|Y)`, and equality occurs if and only if `X` and `Y` are independent random
variables."

**Formalization Note.** The pair `(X, Y)` is its joint distribution `p` on `α × β` (finite
alphabets); `H(X) = entropy p.fst`, `H(X|Y) = condEntropy p` (bits), and independence is
`FinDist.Indep`: `p(x, y) = p_X(x) p_Y(y)` for all `x, y`. -/
theorem condEntropy_le_entropy {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) :
    condEntropy p ≤ entropy p.fst ∧ (condEntropy p = entropy p.fst ↔ p.Indep) := by sorry

end WildeQIT.ZhangAudenaert
