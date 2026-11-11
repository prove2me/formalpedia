-- Prove2me | Theorems.Thm_ReconfRes_Frozen_corollary_3_64
-- name    : ReconfRes.Frozen.corollary_3_64
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:23:40.15196+00:00
-- url     : https://prove2.me/theorems/75e0651e-110f-4a5f-b813-d0fa251229c9
-- title:
--   Corollary 3.64 (= Corollary 1.2) — frozen lean reachability is PSPACE-complete for every k ≥ 2, even on one-copy Horn instances at size 2|H|−1 and input width
-- statement:
--   For every fixed $k\ge2$, frozen lean reachability is PSPACE-complete even for Horn formulas $H$ whose two supplied endpoints each use every clause exactly once as an axiom. Hardness holds at size budget $s=2|H|-1$ and width bound $w=\max_{C\in H}|C|$, with both bounds written in unary. Every proof reachable from either endpoint is a read-once tree without weakening:
--   $$\forall k\ge2:\quad \mathrm{FrozenReach}_k\in\mathrm{PSPACE}\ \ \wedge\ \ \mathrm{FrozenReach}_k\ \text{is PSPACE-hard on one-copy instances}.$$
--   This is the paper's leading result: navigating between minimum-size Horn refutations by bounded local rewrites that keep every axiom node is already as hard as any polynomial-space computation.
--
--   **Formalization Note.** Membership is for the general problem (all $F,w,s,R_1,R_2$). Hardness is `PSPACEHard` over the subtype of instances satisfying `OneCopy k` (Horn, both endpoints vertices with axiom multiset exactly $H$, $s+1=2|H|$, $w=\max_{C\in H}|C|$, every refutation reachable from either endpoint read-once), with encoding `encInstance ∘ Subtype.val`, so every reduction output satisfies the whole promise.
--
--   Differences from the source:
--   - encoding: refutations identified up to renaming of nodes (p. 19, p. 23) → concrete DAGs on Fin n; adjacency is invariant under renaming and connectivity steps include isomorphisms; reason: Lean needs concrete presentations; the components are those of the graph on isomorphism classes
--   - encoding: instances (F, w, s, R₁, R₂) with w, s in unary; PSPACE (§2.3) → encInstance (injective, self-delimiting, w and s unary) and the published InPSPACE / PSPACEHard; reason: the published class counts the input as space, harmless for polynomial bounds
--   - encoding: "PSPACE-complete even for (one-copy instances)" → InPSPACE of the general problem ∧ PSPACEHard over the subtype of one-copy instances; reason: every reduction output satisfies the whole promise
--   - encoding: "use every clause exactly once as an axiom"; s = 2|H| − 1 → axiom multiset = H with multiplicity one; s + 1 = 2|H|; reason: multiset equality is exactly one axiom node per clause and no other; no truncated subtraction
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 83, Corollary 3.64 (informal Corollary 1.2, p. 6)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_Instance

open MultiplierAssoc206.Resolution OptimalQueuingComplexity.Restless

namespace ReconfRes.Frozen

/-- **Corollary 3.64** (one-copy frozen hardness; = Corollary 1.2). For every fixed `k ≥ 2`,
frozen lean reachability (with `w` and `s` in unary) is in PSPACE, and it is PSPACE-hard on the
one-copy instances: Horn formulas `H` whose two endpoints each use every clause exactly once as an
axiom, at size budget `s = 2|H| − 1` and width bound `w = max_{C∈H} |C|`, with every refutation
reachable from either endpoint a read-once tree without weakening. -/
theorem corollary_3_64 (k : ℕ) (hk : 2 ≤ k) :
    InPSPACE encInstance (FrozenReach k) ∧
    PSPACEHard (fun x : {x : Instance // OneCopy k x} => encInstance x.1)
      (fun x : {x : Instance // OneCopy k x} => FrozenReach k x.1) := by sorry

end ReconfRes.Frozen
