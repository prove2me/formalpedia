-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_reduced_parameters_admissible
-- name    : QAlgorithms.Papers.Independent.Support21.P12.reduced_parameters_admissible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:10:43.877729+00:00
-- url     : https://prove2.me/theorems/08c3df8f-3579-4a7e-bf26-414edddfc6cb
-- title:
--   Recurrence and admissibility for the truncated root tuple
-- statement:
--   Let $S$ be an integral domain and let $A_{2,S,r}$ be either actual cyclotomic BMW algebra with its permitted parameters. Assume the whole left ideal $A_2e_1$ is torsion free and Assumption 5.3 holds: $0<d<r$, the parameters are d-semi-admissible, and $p_0(T)=\prod_{i=1}^d(T-u_i)=\sum_{j=0}^d b_jT^j$ satisfies $p_0(y_1)e_1=0$. Then
--
--   $$\sum_{j=0}^d b_j\omega_{j+\ell}=0\quad(\ell\ge0),\qquad
--   (y_1^je_1)_{0\le j<d}\text{ is S-linearly independent in }A_{2,S,d}.$$
--
--   Here the second algebra is the actual smaller cyclotomic quotient with the first d roots and the same remaining parameters. Its admissibility is a conclusion; in the ordinary case no restriction $q^2\ne1$ is added.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 11, Lemma 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 5.5, BOTH clauses, PDF p.11. Admissibility in the smaller
cyclotomic quotient is a conclusion, distinct from independence in the larger one. -/
theorem reduced_parameters_admissible (S : Type*) [CommRing S] [IsDomain S]
    (omega : ℕ → S) (K : Kind S omega) (r : ℕ) (u : Fin r → S)
    (hu : ValidRoots K u) (htor : IdealTorsionFree S omega K r u)
    (d : ℕ) (h : d ≤ r) (hsplit : SplitSemi S omega K r u d h) :
    RootRecurrence omega (firstRoots u h) ∧ CyclicAdmissible S omega K d (firstRoots u h) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
