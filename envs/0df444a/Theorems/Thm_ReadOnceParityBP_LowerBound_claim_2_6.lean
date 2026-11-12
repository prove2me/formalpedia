-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_claim_2_6
-- name    : ReadOnceParityBP.LowerBound.claim_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:27.418117+00:00
-- url     : https://prove2.me/theorems/678537e0-4755-4344-aa85-b83d81baa22a
-- title:
--   Claim 2.6 — algebraic-to-Boolean lower-bound transfer
-- statement:
--   Let f be a multilinear polynomial over F₂ and S a natural number. Suppose that every syntactically multilinear ABP computing f has at least S edges. Then every read-once parity branching program Q computing the Boolean evaluation f_bool satisfies
--
--   $$|Q|\ge S.$$
--
--   The same exact edge threshold is retained. The hypothesis concerns formal polynomial computation, while the conclusion concerns agreement on every Boolean input. This bridges the two models without assuming a lower bound for Q.
--
--   Differences from the source:
--   - generalization: polynomials on finitely many named variables → polynomials indexed by any type; reason: each polynomial and program uses only finitely many variables, so the finite result specializes and extends without additional assumptions
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Claim 2.6, p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_ParityProgram
import Definitions.Def_ReadOnceParityBP_LowerBound_AlgebraicProgram

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Claim 2.6 (p. 5): if a multilinear `f ∈ 𝔽₂[x]` requires syntactically multilinear
ABPs of size `S` (every such ABP computing `f` has at least `S` edges), then `f_bool` requires
read-once ⊕-BPs of size `S`. -/
theorem claim_2_6 {ι : Type} (f : MvPolynomial ι (ZMod 2)) (hf : IsMultilinear f) (S : ℕ)
    (hS : ∀ P : SMABP ι (ZMod 2), P.poly = f → S ≤ P.size) :
    ∀ Q : ParityBP ι, Q.Computes (boolOf f) → S ≤ Q.size := by sorry

end ReadOnceParityBP.LowerBound
