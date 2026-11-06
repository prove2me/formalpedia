-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_corollary_10_7_1
-- name    : WildeQIT.PinskerRefined.corollary_10_7_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:09.652054+00:00
-- url     : https://prove2.me/theorems/14bf4179-8f81-4f0f-87b3-0ae5488fefa7
-- title:
--   Corollary 10.7.1 — $I(X;Y)\ge I(X;Y|Z)$ for $X\to Y\to Z$
-- statement:
--   Let $X,Y,Z$ be discrete random variables on finite alphabets forming a Markov chain $X\to Y\to Z$. Then
--
--   $$
--   I(X;Y)\ge I(X;Y|Z). \tag{10.62}
--   $$
--
--   For a Markov chain, conditioning on the processed variable $Z$ can only decrease the information $Y$ carries about $X$.
--
--   **Formalization Note** Alphabets are finite types, as throughout the book; a random variable is represented by its distribution, and a triple $(X,Y,Z)$ by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits. The Markov chain is the published `IsMarkovChain`: $p(x,y,z)\,p_Y(y)=p_{XY}(x,y)\,p_{YZ}(y,z)$ for all $x,y,z$.
--
--   Differences from the source:
--
--   - encoding: X → Y → Z, p_{Z|Y,X}(z|y,x) = p_{Z|Y}(z|y) (10.55) → IsMarkovChain: p(x,y,z) p_Y(y) = p_XY(x,y) p_YZ(y,z) for all x, y, z; reason: division-free form; conditionals are undefined where p_XY(x,y) = 0 and both forms agree wherever defined
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 10.7.1, p. 302, Eq. (10.62)

import Definitions.Def_WildeQIT_mutualInfo
import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WildeQIT_IsMarkovChain

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Corollary 10.7.1**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 302: for a Markov chain `X → Y → Z`,
`I(X;Y) ≥ I(X;Y|Z)` (10.62).

**Formalization Note** Alphabets are finite types (`Fintype`), as throughout the book; a random variable is represented by its distribution (`FinDist`), a triple `(X, Y, Z)` by its joint law on `α × β × γ` = `α × (β × γ)`. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits (`Real.logb 2`, `0 log 0 = 0`). The Markov chain is the published `IsMarkovChain`; `I(X;Y)` is
`mutualInfo` of the marginal `p_{XY}` and `I(X;Y|Z)` is `condMutualInfo p`. -/
theorem corollary_10_7_1 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) (hp : p.IsMarkovChain) :
    condMutualInfo p ≤ mutualInfo p.margXY := by sorry

end WildeQIT.PinskerRefined
