-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_mutualInfo_nonneg
-- name    : WildeQIT.ZhangAudenaert.mutualInfo_nonneg
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:56:16.371605+00:00
-- url     : https://prove2.me/theorems/963c84eb-4484-48ab-be7c-4657e32b813f
-- title:
--   Theorem 10.4.1: $I(X;Y)\ge0$, with equality iff $X$ and $Y$ are independent
-- statement:
--   Let $X$ and $Y$ be random variables on finite alphabets with joint distribution $p_{X,Y}$, and let $I(X;Y)=H(X)-H(X|Y)$ be their mutual information (Definition 10.4.1, in bits). Then
--
--   $$
--   I(X;Y)\ge 0,
--   $$
--
--   and $I(X;Y)=0$ if and only if $X$ and $Y$ are independent, that is, $p_{X,Y}(x,y)=p_X(x)\,p_Y(y)$ for all $x,y$.
--
--   Mutual information measures the correlation between two random variables; it vanishes exactly on product distributions. This is the classical precursor of strong subadditivity (Theorem 10.6.1).
--
--   **Formalization Note** The pair is represented by its joint distribution on a product of finite types; independence is `FinDist.Indep`.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.4.1, eq. (10.30), p. 296

import Mathlib
import Definitions.Def_WildeQIT_mutualInfo

namespace WildeQIT.ZhangAudenaert

/-- **Theorem 10.4.1 (Non-negativity of mutual information).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.4.1, (10.30),
p. 296: "The mutual information `I(X;Y)` is non-negative for any random variables `X` and `Y`:
`I(X;Y) ≥ 0`, and `I(X;Y) = 0` if and only if `X` and `Y` are independent random variables
(i.e., if `p_{X,Y}(x,y) = p_X(x) p_Y(y)`)."

**Formalization Note.** The pair `(X, Y)` is its joint distribution `p` on `α × β` (finite
alphabets); `I(X;Y) = mutualInfo p = H(X) − H(X|Y)` (Definition 10.4.1, bits), and
independence is `FinDist.Indep`. -/
theorem mutualInfo_nonneg {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) :
    0 ≤ mutualInfo p ∧ (mutualInfo p = 0 ↔ p.Indep) := by sorry

end WildeQIT.ZhangAudenaert
