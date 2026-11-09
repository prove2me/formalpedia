-- Prove2me | Theorems.Thm_QCSepTotal_eq_1
-- name    : QCSepTotal.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:32.301173+00:00
-- url     : https://prove2.me/theorems/08643253-19ca-4adb-9c64-87eb22a99c14
-- title:
--   Eq. (1) — $h^2(P,Q)\le\Delta(P,Q)\le\sqrt2\,h(P,Q)$
-- statement:
--   For distributions $P,Q$ on a common space,
--   $$h^2(P,Q)\le\Delta(P,Q)\le\sqrt2\,h(P,Q),$$
--   where $h=\sqrt{h^2}$ and $h^2(P,Q)=1-\sum_z\sqrt{P(z)Q(z)}$.
--
--   With Fact 1, it converts closeness of transcript distributions on $(x,y)$ and $(x',y')$ into closeness on $(x,y)$ and $(x',y)$ (p.10).
--
--   Differences from the source:
--   - generalization: distributions on a finite space → distributions on any discrete space (PMFs, infinite sums); reason: finite spaces are a special case; p.10 applies (1) to transcript distributions
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §2, p.3, eq. (1)

import Mathlib
import Definitions.Def_QCSepTotal_tv
import Definitions.Def_QCSepTotal_hellingerSq

namespace QCSepTotal

/-- **Eq. (1)** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.3): `h²(P, Q) ≤ Δ(P, Q) ≤ √2 h(P, Q)`, with
`h = √h²`.

**Formalization Note.** Stated for distributions on any (discrete) space, of which the paper's
finite spaces are a special case; it is applied on p.10 to transcript distributions. -/
theorem eq_1 {α : Type*} (P Q : PMF α) :
    hellingerSq P Q ≤ tv P Q ∧ tv P Q ≤ Real.sqrt 2 * Real.sqrt (hellingerSq P Q) := by sorry

end QCSepTotal
