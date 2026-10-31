-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P29_affine_block_iff_central_character
-- name    : QAlgorithms.Papers.Independent.Intake100.P29.affine_block_iff_central_character
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:30:31.16107+00:00
-- url     : https://prove2.me/theorems/549517a6-2f43-42c4-96f0-ee4da667b2fe
-- title:
--   Affine blocks are determined by central characters
-- statement:
--   Let $F$ be algebraically closed, $n\ge1$, and $q\in F^\times\setminus\{1\}$. Let $D,D'$ be nonzero simple finite-dimensional right modules for the extended affine Hecke algebra $\mathcal H_n^{\mathrm{aff}}$. Its centre is the symmetric Laurent polynomial algebra $F[X_1^{\pm1},\ldots,X_n^{\pm1}]^{\mathfrak S_n}$. Then
--
--   $$
--   D\sim_{\mathrm{block},\,\mathcal H_n^{\mathrm{aff}}}D'
--   \quad\Longleftrightarrow\quad
--   \chi_D=\chi_{D'}.
--   $$
--
--   Here a central character records the scalar by which each central symmetric Laurent polynomial acts, and block linkage uses nonsplit extensions in either direction. There are no cyclotomic parameters in this statement, and the affine algebra is not assumed finite dimensional. The paper explicitly acknowledges this as a known consequence of Müller [26, Theorem 7], also [7, III.9].
-- source:
--   Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4, PDF p. 9, Theorem 2.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P29

namespace QAlgorithms.Papers.Independent.Intake100.P29

noncomputable section

open scoped BigOperators Classical

variable {F : Type} [Field F]

/-- Theorem 2.15, PDF p. 9. Known-result provenance: the authors acknowledge
Müller [26, Theorem 7], also Brown--Goodearl [7, III.9]. Only the modules,
not the affine algebra, are finite dimensional. -/
theorem affine_block_iff_central_character [IsAlgClosed F] (m : ℕ)
    (q : F) (hq : q ≠ 0) (hqOne : q ≠ 1)
    (D Dprime : AffineModule F m q) (hD : Simple D) (hDprime : Simple Dprime) :
    Linkage (fun _ => True) (fun _ => True) D Dprime ↔ SameCentralCharacter D Dprime := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P29
