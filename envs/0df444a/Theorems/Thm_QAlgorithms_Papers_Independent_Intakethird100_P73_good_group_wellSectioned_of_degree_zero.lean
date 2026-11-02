-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P73_good_group_wellSectioned_of_degree_zero
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P73.good_group_wellSectioned_of_degree_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:02:51.70894+00:00
-- url     : https://prove2.me/theorems/bd42adfb-12b9-4649-bfab-294bb29a0832
-- title:
--   Partial converse to Proposition 3(1): goodness and the identity section
-- statement:
--   Let $B$ be a weakly Hausdorff k-space and let $G$ be a simplicial group object in $\mathcal K/B$. Thus its levels $G_n$ are parametrized groups and every simplicial structure map is a continuous homomorphism over $B$. Suppose $G$ is good: every degeneracy $s_i:G_n\to G_{n+1}$, for $n\ge0$ and $0\le i\le n$, is a strong $\bar f$-cofibration. If $G_0$ is well-sectioned, then
--
--   $$
--   \forall n\ge0,\qquad 1_{G_n}:B\longrightarrow G_n\text{ is a strong }\bar f\text{-cofibration}.
--   $$
--
--   Here $1_{G_n}$ is the canonical identity section, and well-sectionedness means exactly that this section has the strong cofibration property. Strong cofibrations are defined by their left lifting property against all fiberwise acyclic fiberwise covering-homotopy fibrations in $\mathcal K/B$. No fibrancy hypothesis is imposed on $G$.
--
--   This gives the source's partial converse: goodness propagates well-sectionedness from degree zero to every degree.
-- source:
--   Simplicial principal bundles in parametrized spaces, arXiv:1203.2460v4, PDF p. 13, Partial converse to Proposition 3(1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P73

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P73

open CategoryTheory

open scoped Topology

/-- Roberts--Stevenson, the partial converse following Proposition 3,
arXiv:1203.2460v4, PDF p. 13. A good simplicial parametrized group whose
zero-simplices are well-sectioned is well-sectioned in every degree.
No fibrancy is assumed. -/
theorem good_group_wellSectioned_of_degree_zero
    (B : KSpace) (hB : IsWeaklyHausdorff B) (G : SimplicialParametrizedGroup B)
    (hgood : IsGoodSimplicialGroup G)
    (hzero : IsWellSectioned (G.obj (Opposite.op (SimplexCategory.mk 0)))) :
    ∀ n : ℕ, IsWellSectioned (G.obj (Opposite.op (SimplexCategory.mk n))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P73

end
