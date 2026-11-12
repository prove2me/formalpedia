-- Prove2me | Theorems.Thm_Puder_tracesEachCoreEdgeTwice_of_isAlgExt
-- name    : Puder.tracesEachCoreEdgeTwice_of_isAlgExt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T14:37:47.980742+00:00
-- url     : https://prove2.me/theorems/db12d723-0720-4477-925b-16c6cc1ccf04
-- title:
--   Puder, Lemma 4.1 — for a proper algebraic extension N of ⟨w⟩, the walk of w in Γ_X(N) traces every edge at least twice
-- statement:
--   Let $w \in \mathbf F_d$ and let $N \le \mathbf F_d$ be finitely generated (`Subgroup.FG`) and a proper algebraic extension of $\langle w \rangle$ (`Subgroup.zpowers w`): $\langle w \rangle \le_{alg} N$ (`Puder.IsAlgExt`) and $\langle w \rangle \ne N$. Then the walk of the reduced word of $w$ from the basepoint of the core graph $\Gamma_X(N)$ crosses every edge of $\Gamma_X(N)$ at least twice (`Puder.TracesEachCoreEdgeTwice N w`).
--
--   Puder, p. 14: “**Lemma 4.1.** *Let $w \in \mathbf F_k$ and let $N \le_{f.g.} \mathbf F_k$ be a proper algebraic extension of $\langle w \rangle$. Then the closed walk in $\Gamma_X(N)$ corresponding to $w$ traces every edge at least twice.*”
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 14), Lemma 4.1.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 14, Lemma 4.1

import Mathlib
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore

namespace Puder

theorem tracesEachCoreEdgeTwice_of_isAlgExt {d : ℕ} (w : FreeGroup (Fin d))
    (N : Subgroup (FreeGroup (Fin d))) (hN : N.FG) (halg : IsAlgExt (Subgroup.zpowers w) N)
    (hne : Subgroup.zpowers w ≠ N) : TracesEachCoreEdgeTwice N w := by
  sorry

end Puder
