-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_surjectiveHomomorphism
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.surjectiveHomomorphism
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:59:25.927136+00:00
-- url     : https://prove2.me/theorems/8c471c95-9e00-4a76-a9b8-e2e1be95d71b
-- title:
--   Lemma A.6: Surjective *-homomorphism mu: pure p maps to pure or zero; Tr A≥Tr mu(A) for positive A; mu*(mu(p))=p or mu(p)=0, mu(mu*(mu(p)))=m
-- statement:
--   Let $\mu:\mathcal A\to\mathcal B$ be a surjective unital star homomorphism of finite intrinsic C*-algebras, and let $\mu^*$ be its trace adjoint. In the display $p,q$ are pure states on the respective algebras and $T\ge0$. In addition to the displayed claims, every positive-coefficient orthogonal pure diagonalization of $\mu^*(\rho)$ pushes forward term by term to one of $\rho$, and every such diagonalization of $\rho$ pulls back term by term to one of $\mu^*(\rho)$.
--
--   $$
--   \mu(p)\text{ pure or }0,\quad\operatorname{Tr}T\ge\operatorname{Tr}\mu(T),\quad\mu^*\mu(p)=p\text{ or }\mu(p)=0,\quad\mu\mu^*\mu(p)=\mu(p),\quad\mu\mu^*(q)=q.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 66, Lemma A.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Lemma A.6, PDF pp.66-67: all five assertions for a surjective star homomorphism,
including both directions of the diagonalization correspondence. -/
theorem surjectiveHomomorphism {A B : IntrinsicSystem} (F : Hom A B)
    (hsurj : ∀ T, InBlocks B.block T → ∃ U, InBlocks A.block U ∧ F.map U = T) :
    (∀ p, A.IsPureState p → B.IsPureState (F.map p) ∨ F.map p = 0) ∧
    (∀ T, InBlocks A.block T → T.PosSemidef → T.trace.re ≥ (F.map T).trace.re) ∧
    (∀ p q, A.IsPureState p → B.IsPureState q →
      (intrinsicRestriction A F.map (F.map p) = p ∨ F.map p = 0) ∧
      F.map (intrinsicRestriction A F.map (F.map p)) = F.map p ∧ F.map (intrinsicRestriction A F.map q) = q) ∧
    (∀ (rho : Matrix (Fin B.dim) (Fin B.dim) ℂ), B.IsState rho →
      ∀ (m : ℕ) (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ),
      Diagonalization A (intrinsicRestriction A F.map rho) p P →
      Diagonalization B rho p (fun i => F.map (P i))) ∧
    (∀ (rho : Matrix (Fin B.dim) (Fin B.dim) ℂ), B.IsState rho →
      ∀ (m : ℕ) (p : Fin m → ℝ) (P : Fin m → Matrix (Fin B.dim) (Fin B.dim) ℂ),
      Diagonalization B rho p P →
      Diagonalization A (intrinsicRestriction A F.map rho) p (fun i => intrinsicRestriction A F.map (P i))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
