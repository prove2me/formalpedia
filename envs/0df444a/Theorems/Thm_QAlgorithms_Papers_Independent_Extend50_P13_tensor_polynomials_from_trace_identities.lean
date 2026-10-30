-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_tensor_polynomials_from_trace_identities
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.tensor_polynomials_from_trace_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:50:24.681196+00:00
-- url     : https://prove2.me/theorems/0fdecb8a-4a4e-44e4-8456-2de288c428b3
-- title:
--   Theorem 22: tensor identities and permutation polynomials from trace identities
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $r\ge t\ge1$. Let $p$ be a finite complex linear combination of $t$ ordered output matrix words and products of ordinary traces of input-only words, with each of the $r$ input labels appearing exactly once in every monomial. Output words may be empty; closed trace words are nonempty. Form the constant-coefficient group-algebra element $\beta\in\mathbb C[S_{r+t}]$ by appending a distinct output marker to each output word, treating each traced word as a closed cycle, and inverting the resulting cycle product. Let $h_\alpha$ denote contraction of $\widehat T(\alpha)$ against the $r$ inputs, retaining all $t$ identity-filled output slots.
--
--   For any fixed $\rho\in S_t$, if $p(X)$ is a scalar multiple of $T(\rho)$ for every input tuple, there exists a scalar multilinear pure trace polynomial $q$ and a constant-coefficient $\gamma$ formed from its input trace cycles and the fixed output action $\rho$, such that
--
--   $$p(X)=q(X)T(\rho),\qquad h_\beta(X)=p(X),\qquad h_\gamma(X)=q(X)T(\rho),\qquad \beta-\gamma\in J_d(\mathbb C[S_{r+t}]),$$
--
--   and for every input tuple $X$ and arbitrary output test matrices $Y_1,\ldots,Y_t$,
--
--   $$\operatorname{tr}[\widehat T(\beta-\gamma)(X_1\otimes\cdots\otimes X_r\otimes Y_1\otimes\cdots\otimes Y_t)]=0.$$
--
--   Here $J_d$ is the sum of the independently character-defined isotypic ideals with more than $d$ rows. If $p$ vanishes identically, the same conclusions hold with $\gamma=0$, including $\beta\in J_d$, the full trace identity and $h_\beta=0$. Swaps, fixed permutation outputs, identity outputs, ordinary tensor polynomials, and tensor-trace polynomials are all covered. This is a fixed formal trace-identity consequence, not a tuple-dependent certificate.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 18, Theorem 22: tensor identities and permutation polynomials from trace identities

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Theorem 22 (PDF pp.18–19), including permutation, swap, and tensor identities,
and the proof's tensor-trace extension. The headline range r≥t≥1 is explicit.
SOURCE REPAIR: expand the scalar invariant c in fixed pure trace words before
forming gamma; Eq.83's input-dependent c is not treated as a constant coefficient.
The resulting fixed trace identity lies in the independently defined isotypic ideal,
and its all-output contraction yields the original equation. -/
theorem tensor_polynomials_from_trace_identities {d r t : ℕ} (hd : 0 < d)
    (ht : 1 ≤ t) (hrt : t ≤ r) (p : TensorTracePolynomial r t) :
    (∀ rho : Equiv.Perm (Fin t),
      (∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), ∃ c : ℂ,
        evaluateTensorTrace p X = c • QAlgorithms.Schur.tensorPermutation d t rho) →
      ∃ q : PureTracePolynomial r,
        (∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ),
          evaluateTensorTrace p X = evaluatePureTrace q X •
            QAlgorithms.Schur.tensorPermutation d t rho) ∧
        InAntisymmetricIdeal d (tensorPermutationExpansion p-pureTraceExpansion q rho) ∧
        (∀ (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) (Y : Fin t → (Matrix (Fin d) (Fin d) ℂ)),
          Matrix.trace (groupOperator d
            (tensorPermutationExpansion p-pureTraceExpansion q rho) *
              tensorMatrices (joinSlots X Y)) = 0) ∧
        (∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ),
          hPolynomial (tensorPermutationExpansion p) X = evaluateTensorTrace p X ∧
          hPolynomial (pureTraceExpansion q rho) X = evaluatePureTrace q X •
            QAlgorithms.Schur.tensorPermutation d t rho)) ∧
    ((∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), evaluateTensorTrace p X = 0) →
      InAntisymmetricIdeal d (tensorPermutationExpansion p) ∧
      (∀ (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) (Y : Fin t → (Matrix (Fin d) (Fin d) ℂ)),
        Matrix.trace (groupOperator d (tensorPermutationExpansion p) *
          tensorMatrices (joinSlots X Y)) = 0) ∧
      (∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ),
        hPolynomial (tensorPermutationExpansion p) X = evaluateTensorTrace p X ∧
        hPolynomial (tensorPermutationExpansion p) X = 0)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
