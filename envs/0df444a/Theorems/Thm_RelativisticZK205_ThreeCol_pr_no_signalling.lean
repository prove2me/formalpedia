-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_pr_no_signalling
-- name    : RelativisticZK205.ThreeCol.pr_no_signalling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:22.323265+00:00
-- url     : https://prove2.me/theorems/a5e5811e-f6e9-43fa-a118-efc1aa39a5d4
-- title:
--   Fig. 6 — the PR-box is No-Signalling and its outputs satisfy $x\oplus y=a\wedge b$
-- statement:
--   Let $\mathrm{PR}$ be the PR-box, which on inputs $a,b\in\mathbb F_2$ outputs $(x,y)$ uniformly among the solutions of $x\oplus y=a\wedge b$. Then
--
--   1. $\mathrm{PR}$ is No-Signalling: Alice's output law does not depend on $b$ and Bob's does not depend on $a$;
--   2. for all $a,b,x,y$,
--
--   $$
--   P_{\mathrm{PR}}(x,y\mid a,b)>0\iff x\oplus y=a\wedge b.
--   $$
--
--   The simulators use PR-boxes to compute XOR-shares of products of bits held by different parties; this item records that doing so cannot signal.
--
--   Differences from the source:
--   - encoding: bits in F₂, ⊕ and ∧ → Bool, xor and &&; reason: the same two-element field operations
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.6, Fig. 6 (with Definition 13 and the paragraph "Note: Forster and Wolf…")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_PRBox

namespace RelativisticZK205.ThreeCol

/-- Fig. 6, p.6: the PR-box is No-Signalling, and its output `(x, y)` on inputs `(a, b)` has
positive probability exactly when `x ⊕ y = a ∧ b`. -/
theorem pr_no_signalling :
    IsNoSignalling prBox ∧ ∀ a b x y : Bool, (prBox a b (x, y) ≠ 0 ↔ xor x y = (a && b)) := by sorry

end RelativisticZK205.ThreeCol
