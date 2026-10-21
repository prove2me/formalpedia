-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_degenerate_admissibility_equivalences
-- name    : QAlgorithms.Papers.Independent.Support21.P12.degenerate_admissibility_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:09:21.872194+00:00
-- url     : https://prove2.me/theorems/01e567c2-fb3d-49b5-ba99-82be6be422ba
-- title:
--   Four equivalent degenerate admissibility conditions
-- statement:
--   Let $S$ be a commutative unital ring, $r\ge1$, and $\Omega=(\omega_a)_{a\ge0}$ and $u_1,\ldots,u_r$ arbitrary parameters. Let $N_2$ be the actual degenerate cyclotomic BMW algebra and write $p(T)=\prod_i(T-u_i)=\sum_{j=0}^r a_jT^j$. The following are equivalent:
--
--   1. The indexed family $(y_1^je_1)_{0\le j<r}$ is S-linearly independent.
--   2. The three tagged families $y_1^ae_1y_1^b$, $s_1y_1^ay_2^b$, and $y_1^ay_2^b$, with $0\le a,b<r$, jointly form an S-basis.
--   3. Both scalar systems below hold.
--   4. $\omega_a=\eta_a^+(u_1,\ldots,u_r)$ for every $a\ge0$, using integral evaluation.
--
--   $$\sum_{j=0}^r a_j\omega_{j+\ell}=0\ (\ell\ge0),\qquad
--   \sum_{\mu=0}^{r-j-1}\omega_\mu a_{\mu+j+1}=-2\delta_{r-j\text{ odd}}a_j+\delta_{j\text{ even}}a_{j+1}\ (0\le j<r).$$
--
--   This compares independence in the presented algebra, its specified basis, and both parameter characterizations without characteristic restrictions.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 8, Theorem 3.12

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Theorem 3.12, all FOUR equivalent clauses, PDF p.8. No domain,
characteristic, or nonzero-root assumption is imposed on the degenerate case. -/
theorem degenerate_admissibility_equivalences (S : Type*) [CommRing S]
    (omega : ℕ → S) (r : ℕ) (hr : 0 < r) (u : Fin r → S) :
    (CyclicAdmissible S omega .degenerate r u ↔ @IsIndexedBasis S
      (Cyclotomic S omega (.degenerate : Kind S omega) r u 2)
      (Fin 3 × Fin r × Fin r) inferInstance
      (cyclRing S omega .degenerate r u 2).toAddCommGroup
      (@Algebra.toModule S (Cyclotomic S omega .degenerate r u 2)
        (inferInstance : CommRing S).toCommSemiring
        (cyclRing S omega .degenerate r u 2).toSemiring
        (cyclAlgebra S omega .degenerate r u 2))
      (twoStrandBasisFamily S omega r u)) ∧
    (@IsIndexedBasis S
      (Cyclotomic S omega (.degenerate : Kind S omega) r u 2)
      (Fin 3 × Fin r × Fin r) inferInstance
      (cyclRing S omega .degenerate r u 2).toAddCommGroup
      (@Algebra.toModule S (Cyclotomic S omega .degenerate r u 2)
        (inferInstance : CommRing S).toCommSemiring
        (cyclRing S omega .degenerate r u 2).toSemiring
        (cyclAlgebra S omega .degenerate r u 2))
      (twoStrandBasisFamily S omega r u) ↔
      RootRecurrence omega u ∧ TriangularRelations omega u) ∧
    ((RootRecurrence omega u ∧ TriangularRelations omega u) ↔ RootAdmissible omega u) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
