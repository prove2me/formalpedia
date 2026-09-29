-- Prove2me | Theorems.Thm_RolesForceSeven_no_role_colouring_nine
-- name    : RolesForceSeven.no_role_colouring_nine
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T05:47:11.072986+00:00
-- url     : https://prove2.me/theorems/432d9719-09fd-40d2-8c0d-87cf7d236f9a
-- title:
--   Corollary B: no Steiner triple system on $9$ points has a role colouring
-- statement:
--   Let $S$ be any Steiner triple system on $9$ points (for example the affine plane AG(2, 3)). Then no role function is a role colouring of $S$. This follows from the goal, since $9 \neq 7$; directly, every point of such a system lies on $4$ lines, and three roles cannot be assigned to four lines one-to-one.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3.1, Corollary 3.7 and Proposition 3.4 (AG(2, 3)): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Section 3: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md ; public references: Wikipedia, "Steiner system" (Steiner triple systems, replication number): https://en.wikipedia.org/wiki/Steiner_system ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Octonion" (Fano plane mnemonic for the multiplication of imaginary units): https://en.wikipedia.org/wiki/Octonion

import Mathlib
import Definitions.Def_RolesForceSeven_sts

namespace RolesForceSeven
theorem no_role_colouring_nine (S : STS 9) (role : Fin 9 → Finset (Fin 9) → Fin 3) :
    ¬ RoleColouring S role := by sorry
end RolesForceSeven
