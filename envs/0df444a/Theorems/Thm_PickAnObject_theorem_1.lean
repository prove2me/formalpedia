-- Prove2me | Theorems.Thm_PickAnObject_theorem_1
-- name    : PickAnObject.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:41.043304+00:00
-- url     : https://prove2.me/theorems/591345ae-0848-463e-870e-e6ec853871dc
-- title:
--   Theorem 1 (corrected: lower contour set): an individually rational rule can be sequentialized iff it satisfies monotonic discoverability
-- statement:
--   Let $A$ be a finite set of agents, $O$ a finite set of object types containing the null object $\varnothing$, and $\varphi$ an individually rational rule. Then
--
--   $$\exists\,S:\ S \text{ sequentializes } \varphi \quad\iff\quad \varphi \text{ satisfies monotonic discoverability.}$$
--
--   Here $S$ ranges over menu functions (non-empty initial menus; every later menu inside the agent's previous menu with her previous choice removed), and sequentialization means that the pick-an-object run from $h^{A-\varnothing}$ under straightforward strategies produces $\varphi(P)$ for every profile $P$. Monotonic discoverability (Definition 3) is: for every allocation $\mu$ and profile $P$, either $\varphi(P)=\mu$ or some agent $a^*$ satisfies $\mu(a^*)\ne\varphi_{a^*}(P')$ for every $P'\in\mathcal L(P,\mu)$, where $\mathcal L(P,\mu)$ is the set of profiles that agree with $P$, agent by agent, on the objects weakly above $\mu(a)$ and their order.
--
--   Theorem 1 characterizes the rules that pick-an-object mechanisms can run with truthful (straightforward) agents.
--
--   Differences from the source:
--   - correction: $\mathcal L(P,\mu)=\{P': o\,P_a\,o'\,P_a\,\mu(a)\iff o\,P'_a\,o'\,P'_a\,\mu(a)\}$ as displayed on p.12 → $P'_a$ has the same objects strictly above $\mu(a)$ as $P_a$, in the same order, i.e. $(o\,P_a\,o'\wedge o'\,R_a\,\mu(a))\iff(o\,P'_a\,o'\wedge o'\,R'_a\,\mu(a))$; reason: the printed set makes the theorem false: one agent, $O=\{x,y,\varnothing\}$, $\varphi(P)=x$ iff $x\,P\,\varnothing$ (else $\varnothing$) is individually rational and sequentialized by the single menu $\{x,\varnothing\}$, yet $P=(x,\varnothing,y)$, $\mu=\varnothing$, $P'=(y,\varnothing,x)$ violates the printed Definition 3; the corrected set is the sentence under the display
--   - encoding: strict preferences → rankings $O\simeq\{0,\dots,|O|-1\}$, $\varnothing$ as `none`; the run → its $|A|\cdot|O|+1$-period iterate; the menu-shrinking constraint not imposed at histories other than $h^{A-\varnothing}$ in which an agent has faced no menu, and imposed also at lists whose recorded choice is not in its menu (choice histories are lists without the condition $\omega_j\in\Omega_j$); reason: Lean conventions; the run has stopped after that many periods, and such histories never occur
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, Theorem 1, p.14 (proof App. A, pp.40–42), with Definition 2 (p.11) and Definition 3 (p.13)

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **Theorem 1**, Bó–Hakimov, arXiv:2012.01025v4, p.14 (proof App. A, pp.40–42): "There exists a
pick-an-object mechanism that sequentializes an individually rational rule `φ` if and only if `φ`
satisfies monotonic discoverability."

For every finite set of agents `A`, every finite set of object types `O = Obj ∪ {∅}` and every
individually rational rule `φ`: some menu function sequentializes `φ` (Definition 2) iff `φ`
satisfies monotonic discoverability (Definition 3).

**Formalization Note.** Monotonic discoverability uses the corrected lower contour set
`LowerContour` (the printed p.12 display makes this theorem false; see `LowerContour`). -/
theorem theorem_1 {A Obj : Type*} [Fintype A] [DecidableEq A] [Fintype Obj] [DecidableEq Obj]
    (φ : Rule A Obj) (hIR : IsIndividuallyRational φ) :
    (∃ S : MenuFunction A Obj, Sequentializes S φ) ↔ MonotonicDiscoverability φ := by sorry

end PickAnObject
