-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_full_trace_cycles
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.full_trace_cycles
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:35:39.7035+00:00
-- url     : https://prove2.me/theorems/22367bd8-bed9-4555-a479-488602867210
-- title:
--   Eq.(30): full-trace cycle identity
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $\pi\in S_k$, let $\sigma_1,\ldots,\sigma_\ell$ be its disjoint cycles, including singleton cycles, and let $R_{(a_1\cdots a_m)}=X_{a_1}\cdots X_{a_m}$. With the same permutation convention as Proposition 2,
--
--   $$\operatorname{tr}[T(\pi^{-1})(X_1\otimes\cdots\otimes X_k)]=\prod_{j=1}^{\ell}\operatorname{tr}(R_{\sigma_j}).$$
--
--   The empty tensor case uses the scalar algebra and both empty products equal one. This is the scalar invariant associated with a permutation.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 9, Eq.(30): full-trace cycle identity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Full trace-cycle identity, Eq.30 (PDF p.9), including singleton cycles.
The empty-slot case k=0 is also covered by the literal empty tensor/trace products. -/
theorem full_trace_cycles {d k : ℕ} (hd : 0 < d) (pi : Equiv.Perm (Fin k))
    (X : Fin k → (Matrix (Fin d) (Fin d) ℂ)) :
    Matrix.trace (QAlgorithms.Schur.tensorPermutation d k pi⁻¹ * tensorMatrices X) =
      closedCycleExpression pi X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
