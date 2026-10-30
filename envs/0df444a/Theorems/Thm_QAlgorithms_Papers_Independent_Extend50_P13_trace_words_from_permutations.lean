-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_trace_words_from_permutations
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.trace_words_from_permutations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:34:47.380655+00:00
-- url     : https://prove2.me/theorems/907d23f2-61ee-4e74-a5f6-de0cafe48c81
-- title:
--   Corollary 3: trace words from arbitrary permutations
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $k\ge1$, $\pi\in S_k$, and decompose $\pi$ into disjoint cycles, including fixed points. Write each cycle with its largest entry last. For any slot $q$, let $W_{\pi,q}$ be the product of the $X_i$ along the cycle of $q$, starting at $\pi(q)$ and ending at $q$. Let $C_{\pi,q}$ be the product of ordinary traces of the words of all the other cycles; an empty product is one. Then
--
--   $$\operatorname{tr}_{\ne k}[T(\pi^{-1})(\bigotimes_iX_i)]=C_{\pi,k}W_{\pi,k},\qquad
--   \operatorname{tr}_{\ne\pi(k)}[T(\pi)(\bigotimes_iX_i)]=C_{\pi^{-1},\pi(k)}W_{\pi^{-1},\pi(k)}.$$
--
--   These identities translate arbitrary permutation wirings into trace words without rotating an untraced matrix product.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 9, Corollary 3: trace words from arbitrary permutations

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Corollary 3, Eq.28 (PDF pp.8–9). SOURCE CORRECTION: the printed second
open inverse word is canonically rotated to end at k, although the retained slot is
pi(k). Here that word ends at pi(k). For pi=(123) it is X3 X2 X1, as Proposition 2
requires. Every fixed point still contributes its singleton trace. -/
theorem trace_words_from_permutations {d r : ℕ} (hd : 0 < d)
    (pi : Equiv.Perm (Fin (r+1))) (X : Fin (r+1) → (Matrix (Fin d) (Fin d) ℂ)) :
    partialTraceSlot (Fin.last r)
      (QAlgorithms.Schur.tensorPermutation d (r+1) pi⁻¹ * tensorMatrices X) =
        openCycleExpression pi (Fin.last r) X ∧
    partialTraceSlot (pi (Fin.last r))
      (QAlgorithms.Schur.tensorPermutation d (r+1) pi * tensorMatrices X) =
        openCycleExpression pi⁻¹ (pi (Fin.last r)) X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
