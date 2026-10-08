-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_choiceProb_isRegular
-- name    : RevenueOrdered.Stackelberg.choiceProb_isRegular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:43.012101+00:00
-- url     : https://prove2.me/theorems/ca779cc5-b480-4d96-9b1a-9bdb30ad6362
-- title:
--   Proof of Theorem 4.16, pp. 32–33 — the choice probabilities $\mathcal P((e,q),S)=\tfrac{1}{|B|}[(e,q)\in\mathrm{greedy}_{M'}(R\cup S,L)]$ are regular
-- statement:
--   Let $(M,R,B,c)$ be a Stackelberg Matroid instance, $\mathcal C=B\times\{c_1,\dots,c_k\}$ and $M'$ the auxiliary matroid on $R\cup\mathcal C$. Let $L$ be a linear ordering of $R\cup\mathcal C$ that is non-decreasing in cost ($c(f)$ for $f\in R$, $q$ for $(e,q)\in\mathcal C$) and puts elements of $\mathcal C$ before red elements of equal cost. Define, for $S\subseteq\mathcal C$ and $(e,q)\in\mathcal C$,
--   $$
--   \mathcal P((e,q),S)=\begin{cases}1/|B| & \text{if }(e,q)\in\mathrm{greedy}_{M'}(R\cup S,L),\\0&\text{otherwise,}\end{cases}\qquad \mathcal P(0,S)=1-\sum_{(e,q)\in S}\mathcal P((e,q),S).
--   $$
--   Then $\mathcal P$ is a regular discrete choice model: it satisfies axioms (i), (ii), (iii) and (iv), including axiom (iv) for the no-purchase option.
--
--   This is the first step of the proof of Theorem 4.16; it shows that the Stackelberg Matroid problem is an assortment problem under a regular model, to which the bounds of §3 apply.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 32–33, proof of Theorem 4.16 ("Let us prove that P is a regular discrete choice model")

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace RevenueOrdered.Stackelberg

/-- Regularity of the choice model of the proof of Theorem 4.16 (Berbeglia–Joret,
arXiv:1606.01371v3, pp. 32–33): for every ordering `L` of `R ∪ 𝒞` that is non-decreasing in cost
with `𝒞` before `R` on ties, `𝒫((e, q), S) = 1/|B|·[(e, q) ∈ greedy_{M′}(R ∪ S, L)]` satisfies
axioms (i)–(iv). -/
theorem choiceProb_isRegular {α : Type*} (I : Instance α) (L : List (α ⊕ (α × ℝ)))
    (hL : IsAuxOrder I L) :
    RevenueOrdered.Ratio.IsRegular (choiceProb I L) := by sorry

end RevenueOrdered.Stackelberg
