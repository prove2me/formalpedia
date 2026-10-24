-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_minimal_split_annihilator
-- name    : QAlgorithms.Papers.Independent.Support21.P12.minimal_split_annihilator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:10:01.096627+00:00
-- url     : https://prove2.me/theorems/6742571f-5894-473e-a5dc-54b1334b6108
-- title:
--   Construction of the minimal monic split annihilator
-- statement:
--   Let $S$ be an integral domain and let $A_2$ be either actual cyclotomic BMW algebra of degree $r\ge1$, with all the ordinary unit and compatibility conditions when appropriate. Suppose the whole left ideal $A_2e_1$ is torsion free, and the parameters are d-semi-admissible: $0<d<r$, the cyclic family through degree $d-1$ is independent, and the family through degree d is dependent. There is a permutation of the root list, retaining multiplicities, such that
--
--   $$p_0(T)=\prod_{i=1}^d(T-u_i),\qquad p_0(y_1)e_1=0,\qquad \deg p_0=d.$$
--
--   The polynomial is monic, and $f(y_1)e_1\ne0$ for every nonzero $f\in S[T]$ with $\deg f<d$. The root permutation and monic annihilator are conclusions, providing the subsequent standing choice of Assumption 5.3.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 11, Unnumbered minimal split annihilator before Assumption 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Minimal split annihilator constructed before Assumption 5.3, PDF p.11.
The root permutation is a CONCLUSION, and preserves repeated-root multiplicity.
No monic annihilator is assumed in this theorem. -/
theorem minimal_split_annihilator (S : Type*) [CommRing S] [IsDomain S]
    (omega : ℕ → S) (K : Kind S omega) (r : ℕ) (u : Fin r → S)
    (hu : ValidRoots K u) (htor : IdealTorsionFree S omega K r u)
    (d : ℕ) (hsemi : SemiAdmissible S omega K r u d) :
    ∃ sigma : Equiv.Perm (Fin r), ∃ h : d ≤ r,
      let v : Fin d → S := fun i => u (sigma ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
      Polynomial.aeval (cy S omega K r u 2) (rootPolynomial v) * ce S omega K r u 2 0 = 0 ∧
      (rootPolynomial v).Monic ∧ (rootPolynomial v).natDegree = d ∧
      (∀ f : Polynomial S, f ≠ 0 → f.natDegree < d →
        Polynomial.aeval (cy S omega K r u 2) f * ce S omega K r u 2 0 ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
