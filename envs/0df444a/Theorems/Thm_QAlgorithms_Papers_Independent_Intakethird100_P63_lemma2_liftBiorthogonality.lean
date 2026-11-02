-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_lemma2_liftBiorthogonality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.lemma2_liftBiorthogonality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:36:19.588216+00:00
-- url     : https://prove2.me/theorems/20b9710d-9253-4c08-aeb1-ba5c0419b5dd
-- title:
--   Lemma 2: biorthogonality lifts from 1|2 to 1|23
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. A discrete ensemble may have finitely or countably many components: its weights $w_k$ are nonnegative and sum to one, and each component with $w_k>0$ is a normalized density operator. Every mixture below is the computed trace-norm convergent sum $\rho=\sum_k w_k\rho^k$. All component conditions concern positive-weight labels only.
--
--   Let the ensemble be tripartite and suppose for every distinct active pair $k,l$ that $\rho_1^k\rho_1^l=0$ and $\rho_2^k\rho_2^l=0$. Then
--
--   $$\rho_1^k\rho_1^l=0,\qquad\rho_{23}^k\rho_{23}^l=0\qquad(k\ne l,\ w_kw_l>0).$$
--
--   The products are ordinary operator products and all marginals are partial traces. Thus the same decomposition is biorthogonal for the bipartition $1|23$. No entropy-finiteness or SSA-equality premise is needed.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 5, Lemma 2: biorthogonality lifts from 1|2 to 1|23

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Lemma 2, PDF pp.5–6, (13): biorthogonality lifts from 1|2 to 1|23.
No entropy, entropy-finiteness, or component SSA premise is needed. -/
theorem lemma2_liftBiorthogonality (e : DiscreteDensityEnsemble (Fin 3 → ℕ))
    (hbio : Biorthogonal e {0} {1}) : Biorthogonal e {0} {1, 2} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
