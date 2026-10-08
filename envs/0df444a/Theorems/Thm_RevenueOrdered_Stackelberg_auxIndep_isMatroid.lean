-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_auxIndep_isMatroid
-- name    : RevenueOrdered.Stackelberg.auxIndep_isMatroid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:43.30389+00:00
-- url     : https://prove2.me/theorems/10668041-43cb-40df-b2ed-230d7760f4ef
-- title:
--   Proof of Theorem 4.16, p. 32 — the auxiliary system $M'$ on $R\cup\mathcal C$ is a matroid
-- statement:
--   Let $(M,R,B,c)$ be a Stackelberg Matroid instance with distinct red costs $c_1<\dots<c_k$, and $\mathcal C=B\times\{c_1,\dots,c_k\}$. Call $X\subseteq R\cup\mathcal C$ independent if
--
--   1. for each $e\in B$, $X$ contains at most one pair $(e,q)$ with $q\in\{c_1,\dots,c_k\}$, and
--   2. $(R\cap X)\cup\{e\in B:(e,q)\in X\text{ for some }q\}$ is independent in $M$.
--
--   Then there is a matroid $M'$ with ground set $R\cup\mathcal C$ whose independent sets are exactly these sets.
--
--   The paper leaves this check to the reader. $M'$ replaces each blue element by $k$ parallel copies, one per red cost level; in the graphical case it is the graphical matroid of the graph with each blue edge replaced by $k$ parallel edges. The matroid property is what allows Lemma 4.14 to be applied to $M'$.
--
--   **Formalization Note** Elements of $R\cup\mathcal C$ are terms of `α ⊕ (α × ℝ)`; the statement characterises the independent finite sets, which determine a matroid on a finite ground set. The paper's typos in conditions (1) and (2) are corrected as described in the module `Assortment`.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 32, proof of Theorem 4.16 ("We leave it to the reader to check that M′ is indeed a matroid")

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace RevenueOrdered.Stackelberg

/-- The auxiliary system `M′` is a matroid (Berbeglia–Joret, arXiv:1606.01371v3, proof of
Theorem 4.16, p. 32; the paper leaves the check to the reader): there is a matroid on the ground
set `R ∪ 𝒞` whose independent finite sets are exactly the sets satisfying conditions (1) and (2). -/
theorem auxIndep_isMatroid {α : Type*} (I : Instance α) :
    ∃ M' : Matroid (α ⊕ (α × ℝ)), M'.E = (auxGround I : Set (α ⊕ (α × ℝ))) ∧
      ∀ X : Finset (α ⊕ (α × ℝ)), M'.Indep (X : Set (α ⊕ (α × ℝ))) ↔ auxIndep I X := by sorry

end RevenueOrdered.Stackelberg
