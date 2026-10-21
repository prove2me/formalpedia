-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_corollary_1
-- name    : TraceAdopt.LPReform.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:24.021075+00:00
-- url     : https://prove2.me/theorems/03dbfa0f-1f82-4d4d-a0bc-849dbacbf6cb
-- title:
--   Corollary 1, p. 11 — MIN-SCTM equals the weighted LTM seed-set problem
-- statement:
--   For each firm seed set $S_0$, full activation under the SCTM process occurs exactly when the corresponding initial firm vertices eventually activate every vertex of the auxiliary graph $G'$:
--
--   $$S_\infty=N_F\quad\Longleftrightarrow\quad S'_\infty=N'.$$
--
--   Because both optimization problems use the same seed sets and the same objective $\sum_{i\in S_0}w_i$, this is the feasible-set equivalence underlying problem (2).
--
--   **Formalization Note** Eventual full activation is represented by equality with the full finite vertex set at some time. The standing assumptions of §3.1 are included.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 11, Corollary 1, equation (2)

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

/-- Corollary 1, p. 11: feasible seed sets of (1) and (2) coincide. -/
theorem corollary_1 (I : Instance) (hI : I.Standing)
    (S₀ : Finset (Fin I.n)) :
    FullyActivates I S₀ ↔
      ∃ t : ℕ, (ltmStep I)^[t] (liftSeeds I S₀) = Finset.univ := by sorry

end TraceAdopt.LPReform
