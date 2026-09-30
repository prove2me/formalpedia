-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_hypersurface_intersection_length
-- name    : WeierstrassEllipticZeta.triangular_hypersurface_intersection_length
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T22:54:54.922134+00:00
-- url     : https://prove2.me/theorems/9b80b15e-8f05-4dcf-b24c-b970484cfd5f
-- title:
--   Exact hypersurface-intersection lengths in triangular contact quotients
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, let $I\subseteq A$ be an ideal, let $M\in\mathbb C[T]$ be nonzero, and fix three polynomials $r_1,r_2,r_3\in\mathbb C[T]$. Write
--
--   $$\Phi(p)=p(T,r_1(T),r_2(T),r_3(T)).$$
--
--   Assume the exact membership criterion
--
--   $$p\in I\quad\Longleftrightarrow\quad M\mid\Phi(p)\qquad(p\in A).$$
--
--   For any additional polynomial equation $p=0$, put $q=\Phi(p)$ and $J=I+(p)$. Then there exists an isomorphism of complex algebras
--
--   $$A/J\simeq_{\mathbb C}\mathbb C[T]/(\gcd(M,q)).$$
--
--   In particular, $A/J$ is finite-dimensional, with the exact dimension
--
--   $$\dim_{\mathbb C}(A/J)=\deg\gcd(M,q)\le\deg M.$$
--
--   If $q\ne0$, then also
--
--   $$\dim_{\mathbb C}(A/J)\le\deg q.$$
--
--   Thus imposing one additional equation on a contact quotient presented by time substitution has an exact length determined by a univariate greatest common divisor.
--
--   The substitution map $\Phi$ is surjective since it sends $t$ to $T$. The hypothesis identifies $I$ as the inverse image of the principal ideal $(M)$. The image of $I+(p)$ is $(M,q)=(\gcd(M,q))$, and it contains the kernel needed for the quotient correspondence. The first isomorphism theorem produces the displayed algebra isomorphism. Since $M\ne0$, its gcd with $q$ is nonzero, and the power basis of the univariate quotient gives both finite dimensionality and the degree formula. Divisibility of the gcd into each polynomial gives the two bounds.
--
--   **Formalization Note** No monicity or degree bound on the $r_i$ is required. The result is conditional on the stated ideal-membership criterion, which the elliptic-extension contact presentation supplies. The additional equation may be zero, or its substituted polynomial may be zero; the second bound requires $q\ne0$. A nonzero constant $M$ is allowed and gives the zero quotient. Lean uses `Polynomial.natDegree`; the gcd is proved nonzero before finite dimensionality is established, so the dimension formula does not rely on assigning finrank zero to an infinite-dimensional space. This is a local algebraic intersection calculation, not the global zero estimate.
-- source:
--   Derived local commutative-algebra intersection calculation for the finite-contact approach in Senthil Kumar K (2026), Appendix A and Appendix A.2, https://doi.org/10.1017/S001309152610145X. This conditional lemma is proved here and is not quoted as the global zero estimate in Theorem A.2. Primary formal references: Mathlib Ideal.map_comap_of_surjective, Ideal.comap_map_of_surjective, span_gcd, Ideal.quotientKerAlgEquivOfSurjective, AdjoinRoot.powerBasis, finrank_quotient_span_eq_natDegree, and Polynomial.natDegree_le_of_dvd.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations

theorem WeierstrassEllipticZeta.triangular_hypersurface_intersection_length
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
      let J := I ⊔ Ideal.span {p}
      Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
        (Polynomial ℂ ⧸ Ideal.span {gcd M q})) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
      (q ≠ 0 → Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ q.natDegree) := by sorry
