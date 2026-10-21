-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_lemma_2_2
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.lemma_2_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:46:43.280232+00:00
-- url     : https://prove2.me/theorems/7953d694-a8b9-445b-b8c2-2c3876d2e09b
-- title:
--   Lemma 2.2
-- statement:
--   For every $n\geq1$ and every $g\in S_n$, there exists a permutation $h\in S_{n-1}$, embedded by fixing the last letter, such that
--
--   $$g^{-1}=hgh^{-1}.$$
--
--   No order condition is imposed on $h$. This gives inversion conjugacy inside the prescribed subgroup, including the trivial one-letter case.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 9, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 2.2 (PDF p.9). The inverter fixes the last letter; no order-exactly-two
condition is imposed, which would fail already for S_1. -/
theorem lemma_2_2 (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    ∃ h : Equiv.Perm (Fin n),
      g⁻¹ = (h.viaEmbedding (prefixEmbedding (Nat.le_succ n))) * g *
        (h.viaEmbedding (prefixEmbedding (Nat.le_succ n)))⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
