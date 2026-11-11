-- Prove2me | Theorems.Thm_ReconfRes_Frozen_theorem_3_5
-- name    : ReconfRes.Frozen.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:21:28.761557+00:00
-- url     : https://prove2.me/theorems/28b99ba7-7cae-4944-9a87-d9fc10cb32e5
-- title:
--   Theorem 3.5 [IDH+11] — vertex cover reconfiguration (add/remove one vertex, covers of size ≤ K, endpoints ≤ K − 1) is PSPACE-complete
-- statement:
--   The following problem is PSPACE-complete: given a graph $G$, an integer $K$, and two vertex covers $S_s$ and $S_t$ of $G$ of size at most $K-1$, decide whether there is a sequence of vertex covers of $G$, each of size at most $K$, that starts at $S_s$, ends at $S_t$, and in which each cover is obtained from the previous one by adding or removing one vertex:
--   $$\mathrm{VCR}=\{(G,K,S_s,S_t): S_s\leftrightsquigarrow S_t \text{ through covers of size}\le K\}\ \text{is PSPACE-complete}.$$
--   It is the source problem of every hardness reduction of the paper (in its complement form, for independent sets).
--
--   **Formalization Note.** PSPACE, polynomial-time reductions and PSPACE-hardness are the published definitions `OptimalQueuingComplexity_Restless_PSPACEComplete` (multi-stack Turing machines; the input is counted as space, which changes nothing for polynomial bounds). The problem is a promise problem: both membership and hardness are over the subtype of promise instances, with encoding `encVC ∘ Subtype.val`.
--
--   Differences from the source:
--   - encoding: a graph G, an integer K, covers of size at most K − 1 → an adjacency matrix that the promise requires symmetric and irreflexive, K ∈ ℕ, the size condition as |S| + 1 ≤ K, instances restricted to this promise by a subtype; reason: no promise instance has K ≤ 0; the matrix encoding is polynomially equivalent to any standard graph encoding
--   - encoding: PSPACE, polynomial-time many-one reductions (§2.3) → the published InPSPACE / PolyReduces / PSPACEHard on Mathlib TM2 machines, with the instance encoding encVC; reason: the class is a union over all polynomials, so counting the input as space changes nothing
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 23, Theorem 3.5 (citing Ito et al. [IDH+11], proof of Theorem 2)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_ReconfRes_Frozen_VertexCover

open OptimalQueuingComplexity.Restless

namespace ReconfRes.Frozen

/-- **Theorem 3.5** ([IDH+11]). Vertex cover reconfiguration under token addition and removal is
PSPACE-complete: given a graph `G`, an integer `K` and two vertex covers `Ss`, `St` of size at most
`K − 1`, decide whether a sequence of vertex covers of size at most `K` leads from `Ss` to `St`,
adding or removing one vertex per step. Stated over the promise instances (simple graph, endpoint
covers of size at most `K − 1`), encoded by `encVC`. -/
theorem theorem_3_5 :
    PSPACEComplete (fun x : {x : VCInstance // x.Promise} => encVC x.1)
      (fun x : {x : VCInstance // x.Promise} => x.1.Yes) := by sorry

end ReconfRes.Frozen
