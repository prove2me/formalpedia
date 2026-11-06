-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_theorem_10_7_2
-- name    : WildeQIT.PinskerRefined.theorem_10_7_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:06.252986+00:00
-- url     : https://prove2.me/theorems/3fc696c4-b102-45ae-9061-7f53c00d8111
-- title:
--   Theorem 10.7.2 (Data-Processing Inequality) — $I(X;Y)\ge I(X;Z)$ for $X\to Y\to Z$
-- statement:
--   Let $X,Y,Z$ be discrete random variables on finite alphabets forming a Markov chain $X\to Y\to Z$, that is, $p_{Z|Y,X}(z|y,x)=p_{Z|Y}(z|y)$ (10.55). Then
--
--   $$
--   I(X;Y)\ge I(X;Z). \tag{10.56}
--   $$
--
--   Processing $Y$ into $Z$ by a stochastic map that does not look at $X$ cannot increase the information about $X$; this is the form of data processing used in converse proofs.
--
--   **Formalization Note** Alphabets are finite types, as throughout the book; a random variable is represented by its distribution, and a triple $(X,Y,Z)$ by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits. The Markov chain is the published `IsMarkovChain`: $p(x,y,z)\,p_Y(y)=p_{XY}(x,y)\,p_{YZ}(y,z)$ for all $x,y,z$.
--
--   Differences from the source:
--
--   - encoding: X → Y → Z, p_{Z|Y,X}(z|y,x) = p_{Z|Y}(z|y) (10.55) → IsMarkovChain: p(x,y,z) p_Y(y) = p_XY(x,y) p_YZ(y,z) for all x, y, z; reason: division-free form; conditionals are undefined where p_XY(x,y) = 0 and both forms agree wherever defined
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.7.2, p. 302, Eq. (10.56)

import Definitions.Def_WildeQIT_mutualInfo
import Definitions.Def_WildeQIT_IsMarkovChain

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Theorem 10.7.2 (Data-Processing Inequality)**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 302: if `X → Y → Z` is a Markov
chain, then `I(X;Y) ≥ I(X;Z)` (10.56).

**Formalization Note** Alphabets are finite types (`Fintype`), as throughout the book; a random variable is represented by its distribution (`FinDist`), a triple `(X, Y, Z)` by its joint law on `α × β × γ` = `α × (β × γ)`. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits (`Real.logb 2`, `0 log 0 = 0`). The Markov chain is the published `IsMarkovChain`
(`p(x,y,z) p_Y(y) = p_{XY}(x,y) p_{YZ}(y,z)`, the division-free form of (10.55)); `I(X;Y)` and
`I(X;Z)` are `mutualInfo` of the marginals `p_{XY}` and `p_{XZ}`. -/
theorem theorem_10_7_2 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) (hp : p.IsMarkovChain) :
    mutualInfo p.margXZ ≤ mutualInfo p.margXY := by sorry

end WildeQIT.PinskerRefined
