-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_renyi_roof_locking
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.renyi_roof_locking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:36:25.320979+00:00
-- url     : https://prove2.me/theorems/4d181b45-b42d-4c8c-b235-2c87497d2ae9
-- title:
--   Renyi convex-roof entanglement measures admit single-qubit erasure locking
-- statement:
--   Fix $0\le\alpha<1$. On each finite bipartite system let $E_\alpha$ be the convex roof of the Renyi entropy of Alice's marginal of a normalized pure state:
--
--   $$E_\alpha(\rho)=\inf_{\rho=\sum_i p_i|\psi_i\rangle\langle\psi_i|}\sum_i p_i S_\alpha(\operatorname{Tr}_B|\psi_i\rangle\langle\psi_i|).$$
--
--   The infimum runs over all finite ensembles with $p_i\ge0$, $\sum_i p_i=1$ and unit vectors $\psi_i$; at order zero the entropy is logarithmic support rank. For every real $K$, some positive finite cut, two density states $\rho,\sigma$, and $p\in[0,1]$ give the normalized Alice-flagged state $\Omega=p|0\rangle\langle0|\otimes\rho+(1-p)|1\rangle\langle1|\otimes\sigma$ satisfying
--
--   $$E_\alpha(\Omega)-E_\alpha(\operatorname{Tr}_F\Omega)>K.$$
--
--   Thus every roof in this parameter range admits locking by erasure of one local flag qubit.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 4, Examples following Proposition 3

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF p.4, Examples: marginal Renyi convex roofs
at fixed order 0<=alpha<1 admit one-local-qubit erasure locking. The endpoint
zero uses support rank, while the von Neumann order one is excluded. -/
theorem renyi_roof_locking (alpha : ℝ) (ha : 0 ≤ alpha) (hb : alpha < 1) :
    AdmitsLocking (renyiRoof alpha) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
