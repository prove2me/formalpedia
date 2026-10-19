-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_clusterSeparation
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.clusterSeparation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:35:41.311919+00:00
-- url     : https://prove2.me/theorems/031f8c12-8251-46ef-8fac-b00b83329fe4
-- title:
--   Section 2: equivalence classes and separated clusters
-- statement:
--   Let $C_X=\ker H_X$ and $C_Z=\ker H_Z$ be a binary CSS pair satisfying Property 1 with positive constants $c_1,c_2,\delta_0$. Assume $\epsilon_1\ge0$, $2\epsilon_1<\delta_0$, and $4c_1\epsilon_1<c_2$. On $G_z^{\epsilon_1}$ define $x\sim_z y$ when $|x+y|_{C_X^\perp}\le2c_1\epsilon_1n$, with the corresponding definition on $G_x^{\epsilon_1}$ modulo $C_Z^\perp$. Here $|v|_S=\min_{s\in S}|v+s|$. For either basis this is an equivalence relation. Its distinct computed classes are nonempty, pairwise disjoint, and cover the corresponding approximate code. Distinct classes satisfy
--   $$
--   x\in B,\ y\in B',\ B\ne B'\quad\Longrightarrow\quad
--   |x-y|\ge c_2n.
--   $$
--
--   This constructs the separated clusters needed for the depth argument.
--
--   **Formalization Note** The strict domain follows Property 1 on page 2; the page-4 prose writes a non-strict endpoint. The classes are computed from the relation rather than supplied with a separation guarantee.
--
--   **Correction to the printed source.**
--
--   Printed: Page 4 says 'assuming 2 epsilon1 <= delta0', but Property 1 on page 2 is stated only for delta < delta0.
--
--   Corrected: Use 0 <= epsilon1 and the strict inequality 2 epsilon1 < delta0 in the clustering regime.
--
--   Reason: The proof invokes Property 1 at delta = 2 epsilon1; the strict domain is necessary. This is a standing-domain clarification pending independent moderation.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Section 2: equivalence classes and separated clusters, PDF p. 4. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS





























/-- Section 2, PDF p.4: computed equivalence classes partition the approximate words
and are separated. Strict 2*eps1<delta0 is the actual Property-1 domain on p.2. -/
theorem clusterSeparation {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (c1 c2 delta0 eps1 : ℝ) (hcluster : NLTS.ClustersApproximateCodewords C c1 c2 delta0)
    (heps : 0 ≤ eps1) (hdomain : 2*eps1 < delta0) (hsmall : 4*c1*eps1 < c2) :
    ∀ had : Bool,
      Equivalence (fun x y : {y : NLTSWord n // y ∈ nltsApprox C had eps1} =>
        nltsRelated C c1 eps1 had x.val y.val) ∧
      nltsClusterUnion (nltsClasses C c1 eps1 had) = nltsApprox C had eps1 ∧
      (∀ B ∈ nltsClasses C c1 eps1 had, B.Nonempty) ∧
      ∀ B ∈ nltsClasses C c1 eps1 had, ∀ B2 ∈ nltsClasses C c1 eps1 had, B ≠ B2 →
        Disjoint B B2 ∧ ∀ x ∈ B, ∀ y ∈ B2, c2*n ≤ (hammingDist x y : ℝ) := by sorry







end QAlgorithms.Papers.Independent.Independent1.P05
