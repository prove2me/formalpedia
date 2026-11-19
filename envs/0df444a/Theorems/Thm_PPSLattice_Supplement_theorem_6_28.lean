-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_6_28
-- name    : PPSLattice.Supplement.theorem_6_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T09:08:06.804973+00:00
-- url     : https://prove2.me/theorems/691f3511-af36-42fc-a395-974a69e7d120
-- title:
--   Theorem 6.28 — succinct circuit ABE gives robust PPS
-- statement:
--   A selectively secure key-policy circuit ABE whose key size is succinct in circuit size makes Construction 6.27 robustly payload hiding without a bound on queried-set cardinality.
--
--   Differences from the source:
--   - encoding: The source uses circuit attributes and the membership circuit $f_S$ → Lean uses the published Boolean-circuit type, `encvec` attribute encoding, `memCircuit`, and the exact depth bound $d_{N,N}$; reason: these are the already-published encodings used by the base mission's Construction 4.6.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 6.28, p.59

import Mathlib
import Definitions.Def_PPSLattice_Supplement_ABE
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem 6.28**, Goyal--Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f...),
p.59. Selective security of key-policy circuit ABE with keys succinct in circuit size implies
unbounded-set robust payload hiding of Construction 6.27.

**Formalization Note.** Attributes are the published `encvec N i`; set keys use the published
membership circuit with exact depth bound `d_{N,N}`. Key queries remain available on both sides of
the challenge. -/
theorem theorem_6_28 (E : SuccinctABE) (hE : E.IsScheme) :
    (construction627 E).RobustPayloadHiding BitMessage := by sorry

end PPSLattice.Supplement
