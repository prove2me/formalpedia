-- Prove2me | Theorems.Thm_PickAnObject_sp_of_straightforward_pepe
-- name    : PickAnObject.sp_of_straightforward_pepe
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:44.312025+00:00
-- url     : https://prove2.me/theorems/cb241371-bd5b-457c-989d-3ee63659d6c7
-- title:
--   A sequentializing mechanism with a straightforward perfect ex-post equilibrium forces strategy-proofness
-- statement:
--   Let the menu function $S$ sequentialize the rule $\varphi$, and suppose straightforward strategies constitute a perfect ex-post equilibrium of the pick-an-object mechanism $S$. Then $\varphi$ is strategy-proof: for every profile $P$, agent $a$ and preference $P'_a$,
--   $$\varphi_a(P_a,P_{-a})\;R_a\;\varphi_a(P'_a,P_{-a}).$$
--
--   This is the necessity of strategy-proofness in Theorem 2: a profitable misreport would give a profitable deviation at $h^{A-\varnothing}$ (playing straightforwardly for the misreported preference).
--
--   Differences from the source:
--   - generalization: "suppose that $\varphi$ satisfies monotonic discoverability but is not strategy-proof … contradiction" → no monotonic discoverability hypothesis; reason: the argument does not use it; the page's statement is the case where it holds
--   - encoding: argument by contradiction → the contrapositive implication; reason: logically equivalent
--   - encoding: strategies, outcome, histories of $S$ and menu functions as in Lemma 1; reason: the paper's strategy domain (p.18) and run (pp.10–11)
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, App. A, proof of Theorem 2, p.46, first paragraph

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **A straightforward perfect ex-post equilibrium forces strategy-proofness**, Bó–Hakimov,
arXiv:2012.01025v4, App. A, proof of Theorem 2, p.46, first paragraph: "Next, suppose that `φ`
satisfies monotonic discoverability but is not strategy-proof. Moreover, suppose for
contradiction that there is a pick-an-object mechanism `S_φ` that implements `φ` in perfect
ex-post equilibrium. … This is a contradiction with straightforward strategies being a perfect
ex-post equilibrium of the game induced by `S_φ`."

If a menu function `S` sequentializes `φ` and the straightforward type-strategy profile is a
perfect ex-post equilibrium of `S`, then `φ` is strategy-proof.

**Formalization Note.** Stated as the contrapositive of the page's argument by contradiction,
without the monotonic discoverability hypothesis (which the argument does not use). -/
theorem sp_of_straightforward_pepe {A Obj : Type*} [Fintype A] [DecidableEq A] [Fintype Obj]
    [DecidableEq Obj] (φ : Rule A Obj) (S : MenuFunction A Obj) (hS : Sequentializes S φ)
    (hpepe : IsPerfectExPostEquilibrium S straightforwardProfile) :
    IsStrategyProof φ := by sorry

end PickAnObject
