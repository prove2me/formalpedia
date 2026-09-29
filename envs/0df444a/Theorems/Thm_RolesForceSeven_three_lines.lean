-- Prove2me | Theorems.Thm_RolesForceSeven_three_lines
-- name    : RolesForceSeven.three_lines
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T05:43:54.531995+00:00
-- url     : https://prove2.me/theorems/83fe24e5-d626-4e33-8694-a47dc08d1b9a
-- title:
--   A role colouring puts every point on exactly $3$ lines
-- statement:
--   Let $S$ be a Steiner triple system on $[n]$ with a role colouring $\rho$. Then every point $x$ lies on exactly
--
--   $$
--   3
--   $$
--
--   lines. Completeness gives three lines through $x$ with three different roles, so at least $3$; minimality makes "line $\mapsto$ role of $x$ on it" one-to-one into $\{0,1,2\}$, so at most $3$.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3.1, Definition 3.5 (the role postulates force r = 3): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Section 3: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md ; public references: Wikipedia, "Steiner system" (Steiner triple systems, replication number): https://en.wikipedia.org/wiki/Steiner_system ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Octonion" (Fano plane mnemonic for the multiplication of imaginary units): https://en.wikipedia.org/wiki/Octonion

import Mathlib
import Definitions.Def_RolesForceSeven_sts

namespace RolesForceSeven
theorem three_lines (n : ℕ) (S : STS n) (role : Fin n → Finset (Fin n) → Fin 3)
    (h : RoleColouring S role) (x : Fin n) :
    (S.lines.filter (fun l => x ∈ l)).card = 3 := by sorry
end RolesForceSeven
