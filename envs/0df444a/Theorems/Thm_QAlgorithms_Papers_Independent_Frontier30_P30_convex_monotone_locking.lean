-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_convex_monotone_locking
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.convex_monotone_locking
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:34:32.815911+00:00
-- url     : https://prove2.me/theorems/6de738e9-cb67-448a-a983-85fdbe54cab5
-- title:
--   Convex subextensive LOCC monotones that fail asymptotic continuity admit erasure locking
-- statement:
--   Let $E$ be a nonnegative real resource functional on all finite bipartite systems, nonincreasing on average under every selective local quantum instrument and hence adaptive LOCC. Suppose $E$ is convex, and for one uniform $M\ge0$ it satisfies $E(\rho)\le M\log_2(d_A d_B)$. Suppose there is a growing-total-dimension sequence of density pairs on a common cut at each index, approaching in full trace norm, whose $E$-difference divided by the logarithm of total dimension stays bounded below by a positive constant. For every real $K$, there are density states $\rho,\sigma$ on some positive finite cut $A:B$ and $p\in[0,1]$ such that the normalized state
--
--   $$\Omega=p|0\rangle\langle0|_F\otimes\rho+(1-p)|1\rangle\langle1|_F\otimes\sigma,\qquad E(\Omega)-E(\operatorname{Tr}_F\Omega)>K,$$
--
--   where $F$ is one qubit held by Alice. This gives arbitrarily large loss under local erasure, without claiming zero entanglement afterward.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 4, Proposition 3, Eqs. (18)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF p.4, Proposition 3 and (18)--(22).
Locking is erasure: nonselective measurement of the classical flag leaves its
state unchanged. Flagged affinity (19) is not assumed. -/
theorem convex_monotone_locking (E : EntanglementFunctional) (M : ℝ) (hM : 0 ≤ M)
    (hmono : IsLOCCMonotone E) (hconv : IsConvex E)
    (hsub : EntanglementSubextensive E M) (hfailure : EntanglementNoncontinuous E) :
    AdmitsLocking E := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
