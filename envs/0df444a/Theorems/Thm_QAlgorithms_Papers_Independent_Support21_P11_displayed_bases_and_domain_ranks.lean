-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_displayed_bases_and_domain_ranks
-- name    : QAlgorithms.Papers.Independent.Support21.P11.displayed_bases_and_domain_ranks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:04:01.724072+00:00
-- url     : https://prove2.me/theorems/bfe2487a-f6cb-4dac-a2b8-db51e69cfa78
-- title:
--   Displayed bases and integral-domain rank characterizations
-- statement:
--   Let $R$ be a commutative ring with identity, let $r\ge1$, let $\omega=(\omega_a)_{a\ge0}$ be an $R$-valued sequence, and let $u_1,\ldots,u_r\in R$. Write $W$ for the two-strand degenerate cyclotomic BMW algebra with these parameters, $e=e_1$, $s=s_1$, and $x=x_1$. Put $\prod_{i=1}^r(z-u_i)=\sum_{j=0}^r a_jz^j$. Assume $2$ is invertible in $R$. Write $E=(x^ae)_{0\le a<r}$ and let $B$ be the indexed family of the three monomial types $x_1^ae_1x_1^b$, $x_1^ax_2^bs_1$, and $x_1^ax_2^b$, for $0\le a,b<r$. Here admissibility means both $\sum_{\mu=0}^{r-j-1}\omega_\mu a_{\mu+j+1}=-2\delta_{r-j\text{ odd}}a_j+\delta_{j\text{ even}}a_{j+1}$ for $0\le j<r$ and $\sum_{j=0}^ra_j\omega_{j+a}=0$ for every $a\ge0$. If the parameters are admissible, $E$ is an $R$-basis of $We$ and $B$ is an $R$-basis of $W$. If additionally $R$ is an integral domain, each abstract rank condition separately characterizes admissibility:
--
--   $$
--   (\omega,u)\text{ admissible}\ \Longleftrightarrow\ We\cong_R R^r,
--   \qquad
--   (\omega,u)\text{ admissible}\ \Longleftrightarrow\ W\cong_R R^{3r^2}.
--   $$
--
--   The isomorphisms are linear isomorphisms, so these are finite free rank assertions. The first clause identifies the actual displayed bases; the domain assumption applies only to the abstract-rank characterizations.
--
--   **Formalization Note** A displayed basis is expressed by independence of its indexed vectors and equality of its span with the indicated module.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 8, §5, continuation after Theorem 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Continuation after Theorem 5.2, PDF p.8. Displayed families are bases
(encoded by independence and their exact spans). Only the abstract-rank converses
require an integral domain; rank means an actual finite free module isomorphism. -/
theorem displayed_bases_and_domain_ranks (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) (h2 : IsUnit (2 : R)) :
    (BMWAdmissible omega u →
      LinearIndependent R (idealFamily R omega r u) ∧
      leftIdeal R omega r u = Submodule.span R (Set.range (idealFamily R omega r u)) ∧
      LinearIndependent R (algebraFamily R omega r u) ∧
      Submodule.span R (Set.range (algebraFamily R omega r u)) = ⊤) ∧
    (∀ (_ : IsDomain R),
      (BMWAdmissible omega u ↔ Nonempty (leftIdeal R omega r u ≃ₗ[R] (Fin r → R))) ∧
      (BMWAdmissible omega u ↔
        Nonempty (CyclotomicBMW R omega 2 r u ≃ₗ[R] (Fin (3 * r ^ 2) → R)))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
