-- Prove2me | Theorems.Thm_Rank2Sha_tateShafarevich_isTorsion
-- name    : Rank2Sha.tateShafarevich_isTorsion
-- status  : Proved
-- author  : @barindersbanwait
-- created : 2026-11-25T01:11:23.091007+00:00
-- url     : https://prove2.me/theorems/9556fe4a-38a1-4b18-88e9-a17d5b78c4eb
-- title:
--   The Shafarevich–Tate group is a torsion group
-- statement:
--   Let $K$ be a number field and let $E$ be a Weierstrass curve over $K$. Every element of the Shafarevich–Tate group $\text{Ш}(E/K)$ has finite order.
--
--   $$
--   \forall\, x \in \text{Ш}(E/K), \quad \exists\, n \ge 1, \quad n x = 0 .
--   $$
--
--   This holds because $\text{Ш}(E/K)$ is a subgroup of $H^1(G_K, E(\overline{K}))$, the cohomology of a profinite group with coefficients in a discrete module, and such cohomology groups are torsion in positive degree. It reduces finiteness of $\text{Ш}(E/K)$ to statements about its $p$-primary parts.
--
--   **Formalization Note** The group is `W.tateShafarevich` of the definition `Rank2Sha_TateShafarevich`, and the conclusion is `IsAddTorsion`. No nonsingularity hypothesis is needed. A formal proof exists on top of Tau Ceti (`TauCeti.ContinuousCohomology.isAddTorsion_continuousCohomology`, with compactness of the absolute Galois group), for a later version of Lean and Mathlib.
-- source:
--   J.-P. Serre, Galois Cohomology, Springer 1997, https://doi.org/10.1007/978-3-642-59141-9, Chapter I, Section 2.2 (cohomology of a profinite group with discrete coefficients is torsion in positive degree)

import Mathlib
import Definitions.Def_Rank2Sha_TateShafarevich

namespace Rank2Sha
theorem tateShafarevich_isTorsion {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve.Affine K) : IsAddTorsion W.tateShafarevich := by sorry
end Rank2Sha
