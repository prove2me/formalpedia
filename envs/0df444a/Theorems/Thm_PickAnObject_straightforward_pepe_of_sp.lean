-- Prove2me | Theorems.Thm_PickAnObject_straightforward_pepe_of_sp
-- name    : PickAnObject.straightforward_pepe_of_sp
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:39.328619+00:00
-- url     : https://prove2.me/theorems/821b512f-2902-418c-a18e-8b0405e513ba
-- title:
--   Strategy-proofness makes straightforward strategies a perfect ex-post equilibrium of every sequentializing mechanism
-- statement:
--   Let $\varphi$ be a strategy-proof rule and let $S$ be any menu function that sequentializes $\varphi$. Then straightforward strategies constitute a perfect ex-post equilibrium of the pick-an-object mechanism $S$: for every agent $a$, every collective history $h^A$ of $S$ (including $h^{A-\varnothing}$), every strategy $\sigma'_a$ and every profile $P$,
--   $$\mathcal O_a|_{h^A}\bigl(\sigma^P_a,\sigma^P_{-a}\bigr)\;R_a\;\mathcal O_a|_{h^A}\bigl(\sigma'_a,\sigma^P_{-a}\bigr),$$
--   where $\sigma^P$ is the straightforward strategy profile with respect to $P$.
--
--   This is the sufficiency half of Theorem 2: it holds for every sequentializing mechanism, not only for a particular one.
--
--   Differences from the source:
--   - generalization: "if $\varphi$ satisfies monotonic discoverability and is strategy-proof" (for an individually rational $\varphi$) → $\varphi$ strategy-proof only; reason: the argument (Lemma 1 and Corollary 1) uses neither hypothesis; the page's statement is the case where they hold
--   - encoding: "implements $\varphi$ in a perfect ex-post equilibrium in straightforward strategies" → straightforward strategies are a perfect ex-post equilibrium of $S$; reason: $S$ sequentializes $\varphi$ by hypothesis, so this is the remaining part of the implementation notion (p.19)
--   - encoding: strategies → functions of the agent's own history and menu that pick from every non-empty menu; outcome → the $|A|\cdot|O|+1$-period run; histories of $S$ → an inductive reachability predicate; menu functions → `IsMenuFunction` (shrinking constraint at every non-empty list history, none where an agent has faced no menu); reason: the paper's strategy domain (p.18) and run (pp.10–11); menus at histories the mechanism never reaches affect neither the run nor the equilibrium condition
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, App. A, proof of Theorem 2, p.45, last two sentences of the first part

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **Strategy-proofness makes straightforward strategies a perfect ex-post equilibrium of every
sequentializing mechanism**, Bó–Hakimov, arXiv:2012.01025v4, App. A, proof of Theorem 2, p.45,
end of the first part: "Therefore, straightforward strategies constitute an ex-post perfect
equilibrium for the game induced by `S_φ`. Therefore, if `φ` satisfies monotonic
discoverability and is strategy-proof, any pick-an-object mechanism that sequentializes `φ`
implements `φ` in a perfect ex-post equilibrium in straightforward strategies."

If `φ` is strategy-proof, then for every menu function `S` that sequentializes `φ`, the
straightforward type-strategy profile is a perfect ex-post equilibrium of `S`.

**Formalization Note.** Monotonic discoverability and individual rationality are not assumed:
the argument (Lemma 1 and Corollary 1) does not use them, and the page's statement is the special
case in which they hold. -/
theorem straightforward_pepe_of_sp {A Obj : Type*} [Fintype A] [DecidableEq A] [Fintype Obj]
    [DecidableEq Obj] (φ : Rule A Obj) (hsp : IsStrategyProof φ) (S : MenuFunction A Obj)
    (hS : Sequentializes S φ) :
    IsPerfectExPostEquilibrium S straightforwardProfile := by sorry

end PickAnObject
