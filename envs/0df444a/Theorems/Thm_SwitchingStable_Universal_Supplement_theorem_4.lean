-- Prove2me | Theorems.Thm_SwitchingStable_Universal_Supplement_theorem_4
-- name    : SwitchingStable.Universal.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:39:30.148639+00:00
-- url     : https://prove2.me/theorems/d9391a3d-5c7d-4df2-88c5-d4e5401855c1
-- title:
--   Theorem 4 — redundant second witnesses for every predecessor set
-- statement:
--   For every $d\ge2$ and $0\le q<d$, there exist the explicit enhanced and deleted abstract certificate systems $B,D$ of Appendix I, a common distinguished object $z^q$, and a coordinate $i$ with domain size $d$ and value $z^q_i=q$. Both systems are valid and have the same domains and object family. At the boundary $j=q-s+1$ on the left or $j=q+s$ on the right, their witness sets are
--
--   $$W^D_{i,j}(z^q)=\{a_s\}\ \text{or}\ \{b_s\},$$
--   $$W^B_{i,j}(z^q)=\{a_s,a_{s-1}\}\ \text{or}\ \{b_s,b_{s-1}\}\quad(s\ge2).$$
--
--   The two witnesses at each nonadjacent boundary are distinct and exclude $i$. Existing adjacent boundaries have singleton witness sets in both systems. For every predecessor set $P$ excluding $i$,
--
--   $$L_i^B(z^q,P)=L_i^D(z^q,P),\qquad R_i^B(z^q,P)=R_i^D(z^q,P).$$
--
--   Thus both endpoints, and hence the half-open intervals, agree after all second witnesses are deleted. The conclusion includes $q=0$, $q=d-1$, and $d=2$, with the corresponding empty lists or absence of nonadjacent boundaries. This is an abstract obstruction to counting witnesses alone; no realization by a stable market is asserted.
--
--   Differences from the source:
--   - encoding: existential abstract system constructed in Appendix I → enhanced and deleted systems are pinned to the explicit family, with coordinate labels 0,s,q+s; reason: the construction is exactly the source proof and includes all endpoint and empty-list cases
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 38, PDF p. 39, Theorem 4; Section 6 and Appendices G–I

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_Redundancy

namespace SwitchingStable.Universal.Supplement

theorem theorem_4 (d q : ℕ) (hd : 2 ≤ d) (hq : q < d) :
    ∃ B D : Certificate d,
      B = redundantSystem d q true ∧ D = redundantSystem d q false ∧ B.Valid ∧ D.Valid ∧
      B.d = D.d ∧ B.family = D.family ∧
      ∃ (z : Fin d → ℕ) (i : Fin d),
        z = redundantObject d q q ∧ i.val = 0 ∧ z ∈ B.family ∧ z ∈ D.family ∧
        B.d i = d ∧ z i = q ∧
        (∀ j : ℕ, 1 ≤ j → j < d →
          ∃ a b : Fin d, a ≠ i ∧ D.witnesses z i j = {a} ∧
            (if j ≤ q then
              a.val = q - j + 1 ∧ b.val = q - j ∧
                (if j < q then a ≠ b ∧ b ≠ i ∧ B.witnesses z i j = {a, b}
                else B.witnesses z i j = {a})
            else a.val = j ∧ b.val = j - 1 ∧
                (if q + 1 < j then a ≠ b ∧ b ≠ i ∧ B.witnesses z i j = {a, b}
                else B.witnesses z i j = {a}))) ∧
        (∀ P : Finset (Fin d), i ∉ P →
          B.lower z i P = D.lower z i P ∧ B.upper z i P = D.upper z i P) := by sorry

end SwitchingStable.Universal.Supplement
