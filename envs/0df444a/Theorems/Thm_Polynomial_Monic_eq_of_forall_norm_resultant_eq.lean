-- Prove2me | Theorems.Thm_Polynomial_Monic_eq_of_forall_norm_resultant_eq
-- name    : Polynomial.Monic.eq_of_forall_norm_resultant_eq
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:42:22.777278+00:00
-- url     : https://prove2.me/theorems/06e13aad-c863-49c7-b361-2df0093519ce
-- title:
--   A monic polynomial over an ultrametric field is determined by the norms of its resultants: if ‖Res(P, G)‖ = ‖Res(Q, G)‖ for every polynomial G, then P = Q
-- statement:
--   Let $K$ be a field with a nontrivial ultrametric absolute value $\|\cdot\|$ (for example $\mathbb{Q}_p$, $\mathbb{C}_p$, or $\mathbb{F}_q((t))$), and let $P, Q \in K[X]$ be monic. Suppose that
--
--   $$\|\operatorname{Res}(P, G)\| = \|\operatorname{Res}(Q, G)\| \qquad \text{for every } G \in K[X].$$
--
--   Then $P = Q$.
--
--   Here $\operatorname{Res}(P, G)$ is the resultant of $P$ and $G$ with respect to their degrees; for monic $P$ with roots $\alpha_1, \dots, \alpha_n$ (with multiplicity, in an algebraic closure) it equals $\prod_i G(\alpha_i)$ (up to a sign, which does not affect norms). So the statement says that the norms $\|\prod_i G(\alpha_i)\|$, for all $G$, determine the multiset of roots up to the $K$-structure, i.e. determine $P$. This is the resultant form of the lemma used in Tate's isogeny theorem (Milne, Abelian Varieties, Lemma 10.21) to show that the characteristic polynomial of an endomorphism is determined by the $\ell$-adic sizes of $\deg G(\alpha)$; here no Galois closure or splitting is needed.
--
--   Proof idea: for a monic irreducible $\varphi$ with $P = \varphi^d P_1$, $\varphi \nmid P_1$, one has $\operatorname{Res}(P, \varphi + c) = c^{d \deg \varphi} \operatorname{Res}(P_1, \varphi + c)$ for constants $c$, and the second factor is a polynomial in $c$ that is nonzero at $c = 0$, so by the ultrametric inequality its norm is constant for small $c$. Comparing $G = \varphi + c$ and $G = \varphi + c^2$ for a small nonzero $c$ shows that $\varphi$ has the same multiplicity $d$ in $P$ and in $Q$; hence $P$ and $Q$ have the same irreducible factorization.
--
--   **Formalization Note**: $K$ is a `NontriviallyNormedField` with `IsUltrametricDist K` (the norm satisfies $\|x + y\| \le \max(\|x\|, \|y\|)$ and some element has norm $\ne 0, 1$). The resultant is Mathlib's `Polynomial.resultant P G`, whose degree parameters default to `P.natDegree` and `G.natDegree` (Sylvester determinant). The hypotheses are satisfiable (take $Q = P$), so the statement is not vacuous. Example: over $\mathbb{Q}_p$, $P = X$ and $Q = X - p$ are distinguished by $G = X$: $\|\operatorname{Res}(X, X)\| = 0$ while $\|\operatorname{Res}(X - p, X)\| = \|p\| = 1/p$.
-- source:
--   J. S. Milne, Abelian Varieties (course notes, v2.00, 2008), Lemma 10.21 (the polynomial-identification lemma in the proof of Tate's isogeny theorem over finite fields); J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966); resultant form over an ultrametric field without a Galois closure

import Mathlib

set_option autoImplicit false

theorem Polynomial.Monic.eq_of_forall_norm_resultant_eq
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {P Q : Polynomial K} (hP : P.Monic) (hQ : Q.Monic)
    (H : ∀ G : Polynomial K, ‖P.resultant G‖ = ‖Q.resultant G‖) : P = Q := by
  sorry
