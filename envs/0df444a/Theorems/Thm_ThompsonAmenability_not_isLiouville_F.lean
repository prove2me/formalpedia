-- Prove2me | Theorems.Thm_ThompsonAmenability_not_isLiouville_F
-- name    : ThompsonAmenability.not_isLiouville_F
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-30T18:48:14.2378+00:00
-- url     : https://prove2.me/theorems/09b74940-979f-432e-8c2c-2813f086569e
-- title:
--   Kaimanovich — random walks on F with finitely supported strictly non-degenerate steps are not Liouville
-- statement:
--   Let $\mu$ be a finitely supported probability measure on Thompson's group $F$ whose support generates $F$ as a semigroup. Then the random walk $(F, \mu)$ is not Liouville: there is a bounded $\mu$-harmonic function $f$ on $\operatorname{sgr}\mu = F$, meaning $f(g) = \sum_h \mu(h) f(gh)$, that is not constant.
--
--   **Formalization Note.** Kaimanovich proves this (Theorem 35) for an isomorphic copy $\widetilde F$ of $F$ with the product written in the opposite order. The class of measures is closed under $\mu \mapsto \check\mu$, $\check\mu(h) = \mu(h^{-1})$, and harmonic functions for the two orders correspond through $f \mapsto f(\,\cdot^{-1})$, so the statement does not depend on the order. "Not Liouville" is taken, as on the source's p. 8, as the existence of a non-constant bounded $\mu$-harmonic function on $\operatorname{sgr}\mu$, which the Poisson formula makes equivalent to a non-trivial Poisson boundary.
-- source:
--   Kaimanovich, V. A., Thompson's group F is not Liouville, in Groups, Graphs and Random Walks, LMS Lecture Note Ser. 436 (2017) 300–342, https://doi.org/10.1017/9781316576571.013 (arXiv:1602.02971v3, whose page numbers are used), p. 10, end of §1.F (proved as Theorem 35, p. 24)

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_ThompsonAmenability

namespace ThompsonAmenability

theorem not_isLiouville_F (μ : CannonFloydParry.F →₀ ℝ) (hμ : IsProbability μ) (hnd : IsStrictlyNondegenerate μ) :
    ¬ IsLiouville μ := by
  sorry

end ThompsonAmenability
