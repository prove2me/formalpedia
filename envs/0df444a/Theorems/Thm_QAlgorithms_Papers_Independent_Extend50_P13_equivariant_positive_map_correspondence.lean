-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_equivariant_positive_map_correspondence
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.equivariant_positive_map_correspondence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:47:08.539709+00:00
-- url     : https://prove2.me/theorems/dcd6ad47-40f6-4965-a415-3e46d26dee84
-- title:
--   Corollary 17, first clause: equivariant positive-map correspondence
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Fix $r\ge1$ and let $f:M_d^r\to M_d$ be complex multilinear. Then
--
--   $$\begin{aligned}
--   &f(UX_1U^{-1},\ldots,UX_rU^{-1})=Uf(X)U^{-1}\quad\forall U\in U(d),X,\quad f(X)\ge0\quad\forall X_i\ge0\\
--   &\quad\Longleftrightarrow\quad\exists!P:\ f=f_P,\ P\text{ is Hermitian, block positive, and invariant under }U^{\otimes(r+1)}\ \forall U.
--   \end{aligned}$$
--
--   Here $f_P(X)=\operatorname{tr}_{1\ldots r}[P(X_1\otimes\cdots\otimes X_r\otimes I)]$. Block positivity tests all fully separable states. No trace-polynomial representation is an extra hypothesis. This retains the sound first-clause correspondence; the full optimal-witness assertion is separately deferred.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 16, Corollary 17, first clause: equivariant positive-map correspondence

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Corollary 17, first clause (PDF p.16), with the bidirectional correspondence
from p.15. Complex multilinearity is intrinsic to f; no trace-polynomial
representation is assumed as a certificate. The optimal-witness clause is deferred. -/
theorem equivariant_positive_map_correspondence {d r : ℕ} (hd : 0 < d) (hr : 1 ≤ r)
    (f : MultilinearMap ℂ (fun _ : Fin r => (Matrix (Fin d) (Fin d) ℂ)) ((Matrix (Fin d) (Fin d) ℂ))) :
    (ConjugationEquivariant f ∧ PositiveMap f) ↔
      ∃! P : (Matrix (Fin (r+1) → Fin d) (Fin (r+1) → Fin d) ℂ),
        DiagonalUnitaryInvariant P ∧ FullyBlockPositive P ∧ ∀ X, contractInputs P X = f X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
