-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_proposition_3_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.proposition_3_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:58:20.877443+00:00
-- url     : https://prove2.me/theorems/b0d2e76e-d9bf-42a5-9cbf-63e5f6725bca
-- title:
--   All simple two-strand modules annihilated by the contraction
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed.
--
--   Now let $R=\mathbb Q(u_1,\ldots,u_r,q)$, with these $r+1$ generators algebraically independent over $\mathbb Q$. Every nonzero simple unital left $B_{r,2}$-module annihilated by $E_1$ is isomorphic to exactly one of the following models:
--
--   1. A one-dimensional module, indexed by $i\in\{1,\ldots,r\}$ and $\varepsilon\in\{q,-q^{-1}\}$, with
--   $$T_1=\varepsilon,\qquad E_1=0,\qquad X_1=u_i,\qquad X_2=\varepsilon^2u_i.$$
--   2. A two-dimensional module indexed by an unordered pair $\{i,j\}$ of distinct indices. Using $i<j$ to fix its basis, the matrices are
--   $$T_1=\frac{u_j}{u_j-u_i}\begin{pmatrix}\delta&q-u_iq^{-1}u_j^{-1}\\q^{-1}-qu_iu_j^{-1}&-\delta u_iu_j^{-1}\end{pmatrix},\quad E_1=0,\quad X_1=\operatorname{diag}(u_i,u_j),\quad X_2=\operatorname{diag}(u_j,u_i).$$
--
--   All these models exist and are simple; different labels give nonisomorphic modules. There are exactly $2r$ one-dimensional models and $\binom r2$ two-dimensional models. This is the complete classification in the contraction-zero case.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 4, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section TrivialContractionSimples

variable {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ}

/-- Proposition 3.1, PDF p.4: complete classification of simples killed by E_1,
with all four generator actions and exact counts. Model representations exist
as conclusions; they are simple and pairwise nonisomorphic. The linear
intertwiners give the asserted one- or two-dimensional bases of M. -/
theorem proposition_3_1 (P : Ground K r) (hK : IsGenericField P.toRuiXuUnitParameters)
    (M : Type*) [AddCommGroup M] [Module K M]
    (act : RuiXuBMW P 2 →ₐ[K] Module.End K M) (hs : SimpleAction act)
    (he : act (ruiXuE P 2 1) = 0) :
    ∃ one : OneLabel r → (RuiXuBMW P 2 →ₐ[K] Module.End K (Fin 1 → K)),
    ∃ two : TwoLabel r → (RuiXuBMW P 2 →ₐ[K] Module.End K (Fin 2 → K)),
      (∀ l, SimpleAction (one l) ∧ one l (ruiXuE P 2 1) = 0 ∧
        one l (T P 2 1) = heckeEigenvalue P.toRuiXuUnitParameters l.2 • LinearMap.id ∧
        one l (ruiXuX P 2 1 false) = (P.u l.1 : K) • LinearMap.id ∧
        one l (ruiXuX P 2 2 false) =
          ((heckeEigenvalue P.toRuiXuUnitParameters l.2)^2 * (P.u l.1 : K)) • LinearMap.id) ∧
      (∀ l, SimpleAction (two l) ∧ two l (ruiXuE P 2 1) = 0 ∧
        two l (T P 2 1) = (twoTMatrix P.toRuiXuUnitParameters l).mulVecLin ∧
        two l (ruiXuX P 2 1 false) = (twoXMatrix P.toRuiXuUnitParameters l false).mulVecLin ∧
        two l (ruiXuX P 2 2 false) = (twoXMatrix P.toRuiXuUnitParameters l true).mulVecLin) ∧
      (∀ l l', EquivalentActions (one l) (one l') ↔ l = l') ∧
      (∀ l l', EquivalentActions (two l) (two l') ↔ l = l') ∧
      (∀ l m, ¬ EquivalentActions (one l) (two m)) ∧
      ((∃ l, EquivalentActions act (one l)) ∨ (∃ l, EquivalentActions act (two l))) ∧
      Fintype.card (OneLabel r) = 2*r ∧ Fintype.card (TwoLabel r) = Nat.choose r 2 := by sorry

end TrivialContractionSimples

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
