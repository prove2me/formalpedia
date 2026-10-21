-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_deletion_properties
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.deletion_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:03:58.788235+00:00
-- url     : https://prove2.me/theorems/ebf72a7a-2987-472b-a107-90bc70d178bf
-- title:
--   Unnumbered deletion-map identities
-- statement:
--   For $n\geq1$, construct $\widetilde p_n:S_n\to S_{n-1}$ by deleting the last letter from its cycle and retaining all other letters. Then
--
--   $$\widetilde p_n(1)=1,\qquad \widetilde p_n(g)=g\ (g\in S_{n-1}),\qquad \widetilde p_n(g_1hg_2)=g_1\widetilde p_n(h)g_2.$$
--
--   The last identity holds for all $g_1,g_2\in S_{n-1}$ and $h\in S_n$. These are identities of the constructed deletion, without any uniqueness or algebra-homomorphism claim.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 25, Unnumbered deletion-map identities

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Deletion-map identities (PDF p.25) for the constructed cycle deletion.
This does not assert the false uniqueness threshold or multiplicativity. -/
theorem deletion_properties (n : ℕ) :
    deleteLast n 1 = 1 ∧
    (∀ g : Equiv.Perm (Fin n),
      deleteLast n (g.viaEmbedding (prefixEmbedding (Nat.le_succ n))) = g) ∧
    (∀ g1 g2 : Equiv.Perm (Fin n), ∀ h : Equiv.Perm (Fin (n + 1)),
      deleteLast n ((g1.viaEmbedding (prefixEmbedding (Nat.le_succ n))) * h *
        (g2.viaEmbedding (prefixEmbedding (Nat.le_succ n)))) =
        g1 * deleteLast n h * g2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
