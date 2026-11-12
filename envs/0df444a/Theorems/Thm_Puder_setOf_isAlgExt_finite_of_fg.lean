-- Prove2me | Theorems.Thm_Puder_setOf_isAlgExt_finite_of_fg
-- name    : Puder.setOf_isAlgExt_finite_of_fg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T14:00:46.926879+00:00
-- url     : https://prove2.me/theorems/490d9889-6fab-4d4b-956f-f874d4077c0a
-- title:
--   Takahasi — a finitely generated subgroup of F_d has only finitely many algebraic extensions
-- statement:
--   Let $H$ be a finitely generated subgroup of $\mathbf F_d$ (`Subgroup.FG`). Then the set of subgroups $J \le \mathbf F_d$ that are algebraic extensions of $H$ (`Puder.IsAlgExt H J`) is finite.
--
--   Puder, p. 12: “Moreover, if $H \le \mathbf F$ is a finitely generated subgroup, it has only finitely many algebraic extensions in $\mathbf F$. Thus, every group containing $H$ is a free extension of one of finitely many extensions of $H$, which is a well known theorem of Takahasi [Tak51].”
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, §3.1, p. 12), citing M. Takahasi, *Note on chain conditions in free groups*, Osaka Math. J. 3 (1951) 221–225 (no DOI).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 12, §3.1 (Takahasi: a finitely generated subgroup has finitely many algebraic extensions), which cites M. Takahasi, Note on chain conditions in free groups, Osaka Math. J. 3 (1951) 221–225

import Mathlib
import Definitions.Def_StrongConvPuderAlg

namespace Puder

theorem setOf_isAlgExt_finite_of_fg {d : ℕ} (H : Subgroup (FreeGroup (Fin d))) (hH : H.FG) :
    {J : Subgroup (FreeGroup (Fin d)) | IsAlgExt H J}.Finite := by
  sorry

end Puder
