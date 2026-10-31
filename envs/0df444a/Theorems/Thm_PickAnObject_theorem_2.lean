-- Prove2me | Theorems.Thm_PickAnObject_theorem_2
-- name    : PickAnObject.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:42.19835+00:00
-- url     : https://prove2.me/theorems/ad95f5eb-75a5-4c77-85b6-fa1390e00b10
-- title:
--   Theorem 2 (corrected: lower contour set): an individually rational rule is pick-an-object implementable in perfect ex-post equilibrium iff it is strategy-proof and monotonically discoverable
-- statement:
--   Let $A$ be a finite set of agents, $O$ a finite set of object types containing the null object $\varnothing$, and $\varphi$ an individually rational rule. Then
--
--   1. $\varphi$ is pick-an-object implementable in perfect ex-post equilibrium if and only if $\varphi$ is strategy-proof and satisfies monotonic discoverability; and
--   2. if $\varphi$ is pick-an-object implementable in perfect ex-post equilibrium, then for **every** menu function $S$ that sequentializes $\varphi$, straightforward strategies constitute a perfect ex-post equilibrium of $S$.
--
--   Here $\varphi$ is pick-an-object implementable in perfect ex-post equilibrium if some menu function $S$ sequentializes $\varphi$ and straightforward strategies constitute a perfect ex-post equilibrium of $S$, i.e. for every agent $a$, every collective history $h^A$ of $S$ (reachable under arbitrary choices, $h^{A-\varnothing}$ included), every strategy $\sigma'_a$ and every profile $P$,
--   $$\mathcal O_a|_{h^A}\bigl(\sigma^P_a,\sigma^P_{-a}\bigr)\;R_a\;\mathcal O_a|_{h^A}\bigl(\sigma'_a,\sigma^P_{-a}\bigr).$$
--
--   Strategy-proofness and monotonic discoverability thus characterize the individually rational rules that can be run sequentially with truthful choice as a robust equilibrium, and the equilibrium does not depend on which sequentializing mechanism is used.
--
--   Differences from the source:
--   - correction: $\mathcal L(P,\mu)$ of p.12, used by monotonic discoverability (Definition 3) → $P'_a$ has the same objects strictly above $\mu(a)$ as $P_a$, in the same order; reason: the printed set makes Theorem 1, and with it the monotonic-discoverability half of this theorem, false: one agent, $O=\{x,y,\varnothing\}$, $\varphi(P)=x$ iff $x\,P\,\varnothing$ is individually rational, strategy-proof and sequentialized by the single menu $\{x,\varnothing\}$ (with which straightforward play is a perfect ex-post equilibrium), yet $P=(x,\varnothing,y)$, $\mu=\varnothing$, $P'=(y,\varnothing,x)$ violates the printed Definition 3
--   - encoding: strict preferences → rankings $O\simeq\{0,\dots,|O|-1\}$, $\varnothing$ as `none`; strategies → functions of the agent's own history and menu that pick from every non-empty menu; collective histories of $S$ → an inductive reachability predicate including $h^{A-\varnothing}$; the run → its $|A|\cdot|O|+1$-period iterate; the menu-shrinking constraint not imposed at histories other than $h^{A-\varnothing}$ in which an agent has faced no menu, and imposed also at lists whose recorded choice is not in its menu (choice histories are lists without the condition $\omega_j\in\Omega_j$); reason: Lean conventions and the paper's strategy domain (p.18); the run has stopped after that many periods, and such histories never occur
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, Theorem 2, p.19 (proof App. A, pp.43–46), with Definitions 3 (p.13) and 4 (p.19) and the implementability sentence (p.19)

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **Theorem 2**, Bó–Hakimov, arXiv:2012.01025v4, p.19 (proof App. A, pp.43–46): "Let `φ` be an
individually rational rule. Then `φ` is pick-an-object implementable in perfect ex-post
equilibrium if and only if `φ` is strategy-proof and satisfies monotonic discoverability.
Moreover, straightforward strategies constitute a perfect ex-post equilibrium profile for every
pick-an-object mechanism that sequentializes a rule that is pick-an-object implementable in
perfect ex-post equilibrium."

For every finite set of agents `A`, every finite set of object types `O = Obj ∪ {∅}` and every
individually rational rule `φ`:
1. `φ` is pick-an-object implementable in perfect ex-post equilibrium iff it is strategy-proof
   and satisfies monotonic discoverability; and
2. if `φ` is pick-an-object implementable in perfect ex-post equilibrium, then for **every** menu
   function `S` that sequentializes `φ`, straightforward strategies are a perfect ex-post
   equilibrium of `S`.

**Formalization Note.** Monotonic discoverability uses the corrected lower contour set
`LowerContour` (p.12). Perfect ex-post equilibrium is checked at every reachable collective
history (under arbitrary choices, including `h^{A−∅}`), for every profile and every valid
deviation; the run is the `|A|·|O| + 1`-period iterate of the mechanism (see `outcome`). -/
theorem theorem_2 {A Obj : Type*} [Fintype A] [DecidableEq A] [Fintype Obj] [DecidableEq Obj]
    (φ : Rule A Obj) (hIR : IsIndividuallyRational φ) :
    (PAOImplementable φ ↔ IsStrategyProof φ ∧ MonotonicDiscoverability φ) ∧
      (PAOImplementable φ → ∀ S : MenuFunction A Obj, Sequentializes S φ →
        IsPerfectExPostEquilibrium S straightforwardProfile) := by sorry

end PickAnObject
