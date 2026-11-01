-- Prove2me | Theorems.Thm_ProcNetStab_kwarps_iff_kwarpsAlt
-- name    : ProcNetStab.kwarps_iff_kwarpsAlt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:45.485202+00:00
-- url     : https://prove2.me/theorems/fde7462d-9ee4-4083-b508-89b2f36ac3e1
-- title:
--   Definitions A.3 and A.4 of $k$-WARPS are equivalent (corrected: needs $k \ge 1$)
-- statement:
--   Let $g$ be the observed network on the node set $V$, $L : V \to T$ a type map, and $k \ge 1$. Then $g$ satisfies $k$-WARPS (Definition A.3 = Definition 4.1) if and only if it satisfies the alternate form of $k$-WARPS (Definition A.4):
--   $$
--   k \ge 1 \implies \Bigl( g \text{ satisfies } k\text{-WARPS} \iff g \text{ satisfies the alternate form of } k\text{-WARPS} \Bigr).
--   $$
--
--   The alternate form is the one used in the proofs of necessity and sufficiency; this equivalence connects it to the axiom stated in the main text.
--
--   Differences from the source:
--
--   - correction: Definitions A.3 and A.4 are equivalent (for every k) → equivalent for every k ≥ 1 (hypothesis 1 ≤ k); reason: at k = 0 the two-node empty network violates Definition A.3 (i = i′ = 1, j = j′ = 2: 0-neighborhoods are single nodes) while Definition A.4 holds vacuously because g has no links; the printed argument takes x = σ(j′), which needs j′ in the k-neighborhood of i′, i.e. k ≥ 1
--   - generalization: node set N = {1,...,n} and a finite set T of types → arbitrary node type V, arbitrary type space T and type map L : V → T; reason: the finite case is an instance; T = Unit is the untyped Definition 3.4
--   - reading: k-WARPS: "for all pairs of nodes i and j in the network" → i and j arbitrary nodes, not required to be linked or distinct; reason: Definition A.4 and the proof of Lemma 1 use no link ij; restricting to linked or distinct pairs makes Theorem 1 false (n = 5, k = 1, g = {01, 03, 24}, i = j = 0, i′j′ = 12)
--   - encoding: networks (N,E), k-neighborhoods, preference relations ⪰_i ⊂ G × G → SimpleGraph V, the k-ball via the extended distance edist and the induced subgraph, relations pref a x y read as x ⪰_a y; reason: Lean conventions; same instances
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), p.OA-1 (PDF p.30), "These definitions are equivalent"

import Mathlib
import Definitions.Def_ProcNetStab_KWARPS
import Definitions.Def_ProcNetStab_KWARPSAlt

namespace ProcNetStab

/-- **Definitions A.3 and A.4 are equivalent** (Chiong, Qi, *Stability of Procurement Networks*
(authors' manuscript, 2025), p.OA-1 (PDF p.30), "These definitions are equivalent"), corrected to
`1 ≤ k`: for every type map `L`, observed network `g` and `k ≥ 1`, `g` satisfies `k`-WARPS
(Definition A.3 = Definition 4.1) iff it satisfies the alternate form (Definition A.4).

**Formalization Note** The hypothesis `1 ≤ k` is a correction: at `k = 0` the two-node empty
network violates Definition A.3 (take `i = i'`, `j = j'`) while Definition A.4 holds vacuously
because `g` has no links. -/
theorem kwarps_iff_kwarpsAlt {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ)
    (hk : 1 ≤ k) : KWARPS L g k ↔ KWARPSAlt L g k := by sorry

end ProcNetStab
