-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_bmw_base_change
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.bmw_base_change
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:45:50.494002+00:00
-- url     : https://prove2.me/theorems/3504bf3c-14dc-450e-955d-fcb3d3280a41
-- title:
--   Canonical BMW scalar extension
-- statement:
--   Let $S$ be a commutative unital ring, let $r\ge1$, and let $\rho,q,\delta_0,u_1,\ldots,u_r$ be units of $S$. Let $\delta_j\in S$ be specified for every $j\ge0$, with $\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1)$. Write $W_{n,S,r}$ for the algebra with all the affine BMW relations of Definition 2.3 and the relation $\prod_{i=1}^r(y_1-u_i)=0$.
--
--   Let $T$ be another such ground ring, with primed parameters, and let $\psi:S\to T$ be a unital ring homomorphism preserving $\rho,q$, every $\delta_j$, and every $u_i$. Give $T$ its $S$-algebra structure through $\psi$. For every $n\ge0$ there is a $T$-algebra isomorphism
--   $$E:T\otimes_S W_{n,S,r}\ \xrightarrow{\ \sim\ }\ W_{n,T,r}$$
--   sending $1\otimes e_i$, $1\otimes g_i^{\pm1}$, and, when $n\ge1$, $1\otimes y_1^{\pm1}$ to the corresponding generators. Its inverse sends those generators to the displayed tensors. The restriction $x\mapsto E(1\otimes x)$ is the generator-preserving coefficient map. No injectivity, surjectivity, flatness, admissibility, or domain assumption is imposed on $\psi$.
--
--   This identifies specialization of the presented algebra with extension of scalars. The tensor factors are interchanged from the printed display by the canonical tensor symmetry.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 27, Remark 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Remark 3.3, PDF p.27: canonical coefficient extension without flatness or
injectivity assumptions. Factors are commuted to S' tensor_S W so the
left-factor algebra structure is the S'-algebra structure. Values on all
generators specify the coefficient map and the inverse isomorphism. -/
theorem bmw_base_change {S T : Type*} [CommRing S] [CommRing T] {r : ℕ}
    (P : GroundParameters S r) (Q : GroundParameters T r) (psi : S →+* T)
    (hrho : psi (P.rho : S) = (Q.rho : T))
    (hq : psi (P.q : S) = (Q.q : T))
    (hdelta : ∀ j : ℕ, psi (P.delta j) = Q.delta j)
    (hu : ∀ j : Fin r, psi (P.u j : S) = (Q.u j : T)) (n : ℕ) :
    letI : Algebra S T := psi.toAlgebra
    ∃ E : (T ⊗[S] BMW P n) ≃ₐ[T] BMW Q n,
      (∀ i : ℕ, i + 1 < n → E (1 ⊗ₜ[S] bmwE P n i) = bmwE Q n i) ∧
      (∀ i : ℕ, i + 1 < n → ∀ inverse : Bool,
        E (1 ⊗ₜ[S] bmwG P n i inverse) = bmwG Q n i inverse) ∧
      (1 ≤ n → ∀ inverse : Bool,
        E (1 ⊗ₜ[S] bmwY P n inverse) = bmwY Q n inverse) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
