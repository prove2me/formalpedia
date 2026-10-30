-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_invariant_trace_polynomial_correspondence
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.invariant_trace_polynomial_correspondence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:46:11.413082+00:00
-- url     : https://prove2.me/theorems/de440ee0-e303-47d3-8191-faf77754570e
-- title:
--   Theorem 16, first clause and bidirectional proof: invariant block-positive correspondence
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Fix $r\ge1$. An evaluated function $f:M_d^r\to M_d$ is a multilinear trace polynomial if it is a finite complex linear combination of products of one ordered open matrix word and ordinary traces of closed words, with every input label occurring once in total. Empty open words mean $I$. Then
--
--   $$[f\text{ is such a trace polynomial and }f(X)\ge0\text{ for all PSD tuples }X]
--   \Longleftrightarrow
--   [\exists!P:\ f=f_P,\ P\text{ is block positive and }U^{\otimes(r+1)}P(U^\dagger)^{\otimes(r+1)}=P\ \forall U\in U(d)].$$
--
--   Here $f_P(X)=\operatorname{tr}_{1\ldots r}[P(X_1\otimes\cdots\otimes X_r\otimes I)]$, and block positivity includes Hermiticity and all fully separable product tests. Uniqueness concerns physical $P$, not polynomial syntax or raw group-algebra coefficients. This is the first-clause correspondence; the defective optimal-witness clause is separately deferred.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 15, Theorem 16, first clause and bidirectional proof: invariant block-positive correspondence

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Theorem 16, first clause and both directions of its proof (PDF p.15).
Correspondence is between evaluated maps and physical operators: uniqueness of
raw trace-polynomial syntax or group-algebra coefficients is not asserted. The
separately deferred optimal-witness clause is not included. -/
theorem invariant_trace_polynomial_correspondence {d r : ℕ} (hd : 0 < d) (hr : 1 ≤ r)
    (f : (Fin r → (Matrix (Fin d) (Fin d) ℂ)) → (Matrix (Fin d) (Fin d) ℂ)) :
    (IsTracePolynomial f ∧ PositiveMap f) ↔
      ∃! P : (Matrix (Fin (r+1) → Fin d) (Fin (r+1) → Fin d) ℂ),
        DiagonalUnitaryInvariant P ∧ FullyBlockPositive P ∧ ∀ X, contractInputs P X = f X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
