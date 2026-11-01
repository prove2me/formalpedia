-- Prove2me | Theorems.Thm_WildeQIT_Feedback_theorem_10_7_2
-- name    : WildeQIT.Feedback.theorem_10_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:35:55.440269+00:00
-- url     : https://prove2.me/theorems/5051b048-710b-4d5d-9fcc-f842a698c865
-- title:
--   Theorem 10.7.2 (Data-Processing Inequality) — $I(X;Y)\ge I(X;Z)$ for $X\to Y\to Z$
-- statement:
--   Let $X,Y,Z$ be discrete random variables on finite alphabets forming a Markov chain $X\to Y\to Z$, that is, $p_{Z|Y,X}(z|y,x)=p_{Z|Y}(z|y)$ (10.55). Then
--
--   $$
--   I(X;Y)\ge I(X;Z). \tag{10.56}
--   $$
--
--   Processing $Y$ into $Z$ by a stochastic map that does not look at $X$ cannot increase the information about $X$; this is the form of data processing used in the converse proof of the channel capacity theorem.
--
--   **Formalization Note** A triple $(X,Y,Z)$ is represented by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$; the Markov chain is the published `IsMarkovChain`, $p(x,y,z)\,p_Y(y)=p_{XY}(x,y)\,p_{YZ}(y,z)$ for all $x,y,z$; mutual informations are the published `mutualInfo`, in bits. The same statement is drafted as `WildeQIT.PinskerRefined.theorem_10_7_2` in mission VI and `WildeQIT.ShannonCapacity.theorem_10_7_2` in mission XIII; it is restated here because drafts cannot import drafts.
--
--   Differences from the source:
--   - encoding: X → Y → Z, p_{Z|Y,X}(z|y,x) = p_{Z|Y}(z|y) (10.55) → IsMarkovChain: p(x,y,z) p_Y(y) = p_XY(x,y) p_YZ(y,z) for all x, y, z; reason: division-free form; conditionals are undefined where p_XY(x,y) = 0 and both forms agree wherever defined
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.7.2, p. 302, eq. (10.56)

import Definitions.Def_WildeQIT_mutualInfo
import Definitions.Def_WildeQIT_IsMarkovChain

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.7.2, p. 302.
-/

namespace WildeQIT.Feedback

/-- **Theorem 10.7.2 (Data-Processing Inequality).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.7.2, (10.56),
p. 302: if three random variables `X, Y, Z` form a Markov chain `X → Y → Z`, then
`I(X;Y) ≥ I(X;Z)`.

**Formalization Note.** The triple `(X, Y, Z)` is its joint distribution `p` on `α × β × γ`
(finite alphabets). The Markov chain is the published `IsMarkovChain`
(`p(x,y,z) p_Y(y) = p_{XY}(x,y) p_{YZ}(y,z)`, the division-free form of (10.55));
`I(X;Y)` and `I(X;Z)` are the published `mutualInfo` of the marginals `p_{XY}` and `p_{XZ}`, in
bits. The same statement is drafted in mission VI; it is restated here because drafts cannot
import drafts. -/
theorem theorem_10_7_2 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) (hp : p.IsMarkovChain) :
    mutualInfo p.margXZ ≤ mutualInfo p.margXY := by sorry

end WildeQIT.Feedback
