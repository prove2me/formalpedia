-- Prove2me | Theorems.Thm_RolesForceSeven_roles_force_seven
-- name    : RolesForceSeven.roles_force_seven
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T05:44:52.668975+00:00
-- url     : https://prove2.me/theorems/f19998ef-e626-41d5-a54c-4722fff84dc3
-- title:
--   The role postulates force exactly seven points
-- statement:
--   Let $n \ge 1$. Let $S$ be a Steiner triple system on $\{0, \dots, n-1\}$ — every line has exactly $3$ points and every two distinct points lie on exactly one line — and suppose $S$ has a role colouring: the three points of each line get three different roles in $\{0,1,2\}$, every point takes every role at least once, and every point takes every role at most once. Then
--
--   $$
--   n = 7 .
--   $$
--
--   The conclusion is the point count only; it does not assert that $S$ is the Fano plane. The hypothesis $n \ge 1$ is necessary: the empty system satisfies every other condition and has $0$ points.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3.1, Theorem 3.6: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Section 3 (Theorem 3.6 requires a nonempty point set): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md ; public references: Wikipedia, "Steiner system" (Steiner triple systems, replication number): https://en.wikipedia.org/wiki/Steiner_system ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Octonion" (Fano plane mnemonic for the multiplication of imaginary units): https://en.wikipedia.org/wiki/Octonion

import Mathlib
import Definitions.Def_RolesForceSeven_sts

namespace RolesForceSeven
theorem roles_force_seven (n : ℕ) (hn : 0 < n) (S : STS n)
    (role : Fin n → Finset (Fin n) → Fin 3) (h : RoleColouring S role) :
    n = 7 := by sorry
end RolesForceSeven
