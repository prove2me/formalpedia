-- Prove2me | Theorems.Thm_ReconfRes_Frozen_theorem_3_63
-- name    : ReconfRes.Frozen.theorem_3_63
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:24:02.615449+00:00
-- url     : https://prove2.me/theorems/53d343b6-c4b6-4abb-a147-029cd69435d9
-- title:
--   Theorem 3.63 — frozen lean reachability is PSPACE-complete for every k ≥ 2, hard on Horn instances with identical inventories, size 2α − 1, width max + 2
-- statement:
--   For every fixed $k\ge2$, frozen lean reachability is PSPACE-complete for Horn formulas, with unary width and size bounds and identical prescribed axiom inventories at the endpoints. Hardness holds at size $2\alpha-1$ for $\alpha$ source occurrences and at width two above the maximum axiom width, and every reachable proof is a read-once tree without weakening:
--   $$\mathrm{FrozenReach}_k\in\mathrm{PSPACE}\quad\text{and}\quad \mathrm{FrozenReach}_k\ \text{is PSPACE-hard on the prescribed-inventory instances}.$$
--   It is the intermediate result to which private tags are applied twice for Corollary 3.64.
--
--   **Formalization Note.** Membership is for the general problem; hardness is `PSPACEHard` over the subtype of instances satisfying the promise `PrescribedInventory k`, so every reduction output satisfies the whole promise.
--
--   Differences from the source:
--   - encoding: refutations identified up to renaming of nodes (p. 19, p. 23) → concrete DAGs on Fin n; adjacency is invariant under renaming and connectivity steps include isomorphisms; reason: Lean needs concrete presentations; the components are those of the graph on isomorphism classes
--   - encoding: instances (F, w, s, R₁, R₂) with w, s in unary; PSPACE (§2.3) → encInstance (injective, self-delimiting, w and s unary) and the published InPSPACE / PSPACEHard; reason: the published class counts the input as space, harmless for polynomial bounds
--   - encoding: "PSPACE-complete for … (promise)" → InPSPACE of the general problem ∧ PSPACEHard over the subtype of promise instances; reason: every reduction output satisfies the promise
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 82, Theorem 3.63

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_Instance

open MultiplierAssoc206.Resolution OptimalQueuingComplexity.Restless

namespace ReconfRes.Frozen

/-- **Theorem 3.63** (frozen hardness at locality two). For every fixed `k ≥ 2`, frozen lean
reachability (with `w` and `s` in unary) is in PSPACE, and it is PSPACE-hard on the instances with
a Horn formula, endpoints with identical axiom inventories of `α` source occurrences, size budget
`2α − 1`, width two above the maximum axiom width, and every refutation reachable from either
endpoint a read-once tree without weakening. -/
theorem theorem_3_63 (k : ℕ) (hk : 2 ≤ k) :
    InPSPACE encInstance (FrozenReach k) ∧
    PSPACEHard (fun x : {x : Instance // PrescribedInventory k x} => encInstance x.1)
      (fun x : {x : Instance // PrescribedInventory k x} => FrozenReach k x.1) := by sorry

end ReconfRes.Frozen
