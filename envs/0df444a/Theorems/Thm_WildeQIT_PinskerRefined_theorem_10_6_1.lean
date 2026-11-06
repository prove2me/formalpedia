-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_theorem_10_6_1
-- name    : WildeQIT.PinskerRefined.theorem_10_6_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:10.127847+00:00
-- url     : https://prove2.me/theorems/b97eb984-343c-4794-8a75-2d461516b0f9
-- title:
--   Theorem 10.6.1 (Strong Subadditivity) — $I(X;Y|Z)\ge 0$, with equality iff $X-Z-Y$ is Markov
-- statement:
--   Let $X,Y,Z$ be discrete random variables on finite alphabets with joint distribution $p_{XYZ}$, and let $I(X;Y|Z)=H(Y|Z)-H(Y|X,Z)$ be their conditional mutual information (Definition 10.6.1). Then
--
--   $$
--   I(X;Y|Z)\ge 0, \tag{10.38}
--   $$
--
--   and equality holds if and only if $X - Z - Y$ is a Markov chain, that is, $p_{X,Y|Z}(x,y|z)=p_{X|Z}(x|z)\,p_{Y|Z}(y|z)$ for every $z$ with $p_Z(z)>0$.
--
--   This is the classical strong subadditivity of entropy, with its saturation condition; Theorem 10.8.3 refines both parts quantitatively.
--
--   **Formalization Note** Alphabets are finite types, as throughout the book; a random variable is represented by its distribution, and a triple $(X,Y,Z)$ by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits. The Markov condition is the published `IsMarkovChain` applied to the regrouped triple $(X,Z,Y)$, which unfolds to $p(x,y,z)\,p_Z(z)=p_{XZ}(x,z)\,p_{YZ}(y,z)$ for all $x,y,z$.
--
--   Differences from the source:
--
--   - encoding: p_{X,Y|Z}(x,y|z) = p_{X|Z}(x|z) p_{Y|Z}(y|z) → IsMarkovChain of the regrouped triple (X, Z, Y), i.e. p(x,y,z) p_Z(z) = p_XZ(x,z) p_YZ(y,z) for all x, y, z; reason: multiplying by p_Z(z) removes the undefined conditionals at p_Z(z) = 0, where both sides vanish; same condition wherever the book’s is defined
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.6.1, pp. 297–298, Eq. (10.38)

import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WildeQIT_IsMarkovChain

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Theorem 10.6.1 (Strong Subadditivity)**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 297–298: the conditional mutual
information is non-negative, `I(X;Y|Z) ≥ 0` (10.38), and the inequality is saturated if and only if
`X − Z − Y` is a Markov chain, i.e. `p_{X,Y|Z}(x,y|z) = p_{X|Z}(x|z) p_{Y|Z}(y|z)`.

**Formalization Note** Alphabets are finite types (`Fintype`), as throughout the book; a random variable is represented by its distribution (`FinDist`), a triple `(X, Y, Z)` by its joint law on `α × β × γ` = `α × (β × γ)`. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits (`Real.logb 2`, `0 log 0 = 0`). `I(X;Y|Z)` is the published `condMutualInfo` (Definition 10.6.1).
"`X − Z − Y` is a Markov chain" is the published `IsMarkovChain` (`X → Y → Z` with the middle
component screening off) applied to the regrouped triple `(X, Z, Y)`; unfolded, it says
`p(x,y,z) p_Z(z) = p_{XZ}(x,z) p_{YZ}(y,z)` for all `x, y, z`, the division-free form of the book's
condition (both sides vanish when `p_Z(z) = 0`, where the conditionals are undefined). -/
theorem theorem_10_6_1 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) :
    0 ≤ condMutualInfo p ∧
      (condMutualInfo p = 0 ↔
        (p.comap (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm γ β))).IsMarkovChain) := by sorry

end WildeQIT.PinskerRefined
