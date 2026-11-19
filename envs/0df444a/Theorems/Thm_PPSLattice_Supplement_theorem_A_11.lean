-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_A_11
-- name    : PPSLattice.Supplement.theorem_A_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T09:23:10.911226+00:00
-- url     : https://prove2.me/theorems/7c6fb468-f4a9-4c9f-8763-05e4df2e2a35
-- title:
--   Theorem A.11 — bounded-collusion evolving-graph CSS with no public share
-- statement:
--   Under post-key-query payload hiding, Construction 6.17 instantiated with Construction A.5 is an adaptively secure evolving-graph CSS with collusion bound $Q$, unbounded degree, $Q\,\mathrm{poly}(\lambda)$ vertex shares, and no public share.
--
--   Differences from the source:
--   - reading: Definition 6.16 quantifies over graph lengths while this construction fixes the index space to $2^\lambda$ → Lean makes the implicit PPT-execution bound explicit as $L\le 2^\lambda$ in correctness; reason: polynomially many vertices lie in this index space asymptotically and the paper's proof uses exactly that space.
--   - encoding: The paper refers to the two constructions and the embeddings $0,1\in\mathbb F_{2^h}$ by name → Lean packages the exact Construction-A.5 algorithms and Shamir laws, uses canonical $h$-bit encodings of field zero and one, and applies Construction 6.17 to that scheme; reason: the conjunction states adaptive security, Q-linear shares, and empty public share without permitting an unrelated witness.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem A.11, p.71

import Mathlib
import Definitions.Def_PPSLattice_Supplement_QBoundedRPPS
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem A.11**, Goyal--Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f...),
p.71. Under post-key-query payload hiding, Construction 6.17 instantiated with Construction A.5
is an adaptively secure evolving-graph CSS with collusion bound `Q`, unbounded degree,
`Q·poly(λ)` vertex shares, and no public share.

**Formalization Note.** The existential witness is the fully specified Construction-A.5 bundle,
not an arbitrary robust PPS. `construction617Q` is Construction 6.17 with that Q-bounded scheme;
locality is what makes its public share empty. -/
theorem theorem_A_11 (E : PPS)
    (hE : PPSLattice.Supplement.PPS.IsSchemeForPostKey E AppendixFieldMessage) :
    ∃ C : ConstructionA5 E,
      PPSLattice.Supplement.QBoundedRPPS.BoundedAdaptiveRobust C.scheme
          AppendixFieldMessage ∧
      (construction617Q C.scheme).IsScheme ∧
      (construction617Q C.scheme).QLinearSharesUnboundedDegree ∧
      (construction617Q C.scheme).NoPublicShare := by sorry

end PPSLattice.Supplement
