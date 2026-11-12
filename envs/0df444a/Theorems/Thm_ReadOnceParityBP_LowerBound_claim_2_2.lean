-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_claim_2_2
-- name    : ReadOnceParityBP.LowerBound.claim_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:15.699029+00:00
-- url     : https://prove2.me/theorems/c26442ae-0755-4cc7-8d44-d25741c14c5d
-- title:
--   Claim 2.2 — ABP-to-circuit simulation
-- statement:
--   There is one positive integer C such that, for every polynomial f over F₂ and every syntactically multilinear ABP P computing f, there is a well-formed syntactically multilinear arithmetic circuit Γ computing the same formal polynomial with
--
--   $$|\Gamma|\le C|P|.$$
--
--   The constant is uniform over programs and variable sets. Both sizes count edges, so every incoming sum wire is charged and the zero-edge constant case is included. This is the linear simulation needed to transfer a circuit lower bound to ABPs.
--
--   Differences from the source:
--   - generalization: polynomials on finitely many named variables → polynomials indexed by any type; reason: each polynomial and program uses only finitely many variables, so the finite result specializes and extends without additional assumptions
--   - encoding: size O(S), with the proof charging circuit edges → one positive uniform C and wire size at most C·S, including S=0; reason: a zero-edge ABP computes a constant and admits a zero-wire constant circuit
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
--   - encoding: arithmetic DAG circuits with syntactic variable-disjoint products and edge size → topologically ordered gate lists, finite sum gates, binary products, and the total number of incoming wires; reason: topological numbering preserves sharing and syntactic supports; replacing larger products by binary trees preserves disjointness and changes wire size by at most a constant factor, absorbed in O and Ω
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Claim 2.2 and proof, p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_AlgebraicProgram
import Definitions.Def_ReadOnceParityBP_LowerBound_Circuit

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Claim 2.2 (p. 4): a polynomial over `𝔽₂` computed by a syntactically multilinear ABP
of size `S` is computed by a syntactically multilinear circuit of size `O(S)`, with one
positive constant `C` for all programs. Size counts wires, including sum-gate wires;
zero-edge constant programs admit zero-edge constant circuits. -/
theorem claim_2_2 :
    ∃ C : ℕ, 0 < C ∧ ∀ {ι : Type} (f : MvPolynomial ι (ZMod 2)) (P : SMABP ι (ZMod 2)),
      P.poly = f →
      ∃ Γ : Circuit ι (ZMod 2), Γ.WellFormed ∧ Γ.SyntacticallyMultilinear ∧ Γ.Computes f ∧
        Γ.size ≤ C * P.size := by sorry

end ReadOnceParityBP.LowerBound
