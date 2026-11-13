-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_local_graph
-- name    : SubspaceEvasion312.Explicit.local_graph
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:52.581565+00:00
-- url     : https://prove2.me/theorems/03ddfab7-5baf-4bbd-9650-0fe17caee39e
-- title:
--   Theorem 9 — deterministic local evasive graphs
-- statement:
--   There is an absolute $K>0$. For every finite field $F_q$ and fixed enumeration of its elements, one finite program takes all positive integer parameters $s,b,r,d$ satisfying $(s+b+d)r<bd$, and produces the complete table of the specified conditional-expectation function $f:F_q^s\to F_q^b$. Its graph obeys
--
--   $$G^f\text{ is }(r,d-1)\text{ subspace evasive},\qquad T\le K q^{(s+b)(r+1)+rd}d.$$
--
--   All enumeration, score minimization, preprocessing and output are included in this execution bound. Natural registers stay below $q^{(s+b+r+d+1)^3}$. Repeated projected inputs contribute zero conditional probability. This is the local construction used at every global ambient dimension; its cost is constant in that dimension, with dependence on the fixed parameters retained.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: deterministic conditional-expectation construction in O(q^((s+b)(r+1)+rd) d) time → one parameter-uniform finite program realizing the defined local map, with an absolute multiplier and the trailing factor d; reason: the function is fixed by exhaustive vector and coefficient enumeration and deterministic minimum-score choices; actual transitions and the full local table are charged, not supplied by an oracle
--   - encoding: the proof sums bad events over subspace and subset pairs → the deterministic score sums ordered generating-vector and coefficient-vector descriptions, allowing repeated descriptions; reason: every bad d-point configuration is represented, collisions of input coordinates have zero probability, and the same q^((s+b)r+rd) count bounds the descriptions; repetitions only change the deterministic choice among the valid functions whose existence the source asserts
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 9, printed p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; proof continued printed p. 9 (PDF p. 10)

import Definitions.Def_SubspaceEvasion312_Explicit_local_search

namespace SubspaceEvasion312.Explicit
/-- Theorem 9, printed p.8 (PDF p.9). The same program takes all four
integer parameters; producing the entire local table, including setup, is charged. -/
theorem local_graph :
    ∃ K : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] [Fintype F] (alphabet : List F),
      alphabet.Nodup → (∀ a : F, a ∈ alphabet) →
    ∃ P : Program F, ∀ s b r d : ℕ,
      0 < s → 0 < b → 0 < r → 0 < d → (s+b+d)*r < b*d →
      Evasive (F := F) (graph (localFunction alphabet s b r d)) r (d-1) ∧
      RunsWithin P [s,b,r,d] []
        (K * (Fintype.card F)^((s+b)*(r+1)+r*d) * d)
        (localWordBound (Fintype.card F) s b r d)
        (localTableData alphabet s b r d) := by sorry
end SubspaceEvasion312.Explicit
