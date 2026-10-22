-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_real_schur_algebras
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.real_schur_algebras
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:03:22.627347+00:00
-- url     : https://prove2.me/theorems/94baff92-54d4-4d54-b4de-cca925776add
-- title:
--   Corollary 1.10
-- statement:
--   Let $S$ be a finite-dimensional full irreducible real $\operatorname{Cl}_{p,q}$-module, $p+q>0$, and let $C_{p,q}$ be the real algebra of endomorphisms commuting with the even Clifford action. With $s=p-q$ modulo eight,
--   $$\begin{array}{c|cccccccc}s&1&2&3&4&5&6&7&0\\\hline C_{p,q}&\operatorname{Mat}_2(\mathbb R)&\operatorname{Mat}_2(\mathbb C)&\mathbb H&\mathbb H\oplus\mathbb H&\mathbb H&\mathbb C&\mathbb R&\mathbb R\oplus\mathbb R\end{array}$$
--   Every entry is an isomorphism of real algebras. The type has period eight in $s$ and is unchanged by $(p,q)\mapsto(8k-q,8k-p)$ whenever both literal signatures are nonzero. This is the abstract Schur-algebra classification, with matrix sizes retained.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 16, Corollary 1.10

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Corollary 1.10, PDF p. 16: exact real Schur algebra table and its mirror symmetry. -/
theorem real_schur_algebras :
    (∀ (p q : ℕ), 0 < p + q →
      ∀ (S : Type) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
        (rho : SpinRepresentation (signatureMatrix p q) S),
        HasSchurTable (schurAlgebra rho) ((p : ℤ) - q)) ∧
    (∀ p q k : ℕ, p ≤ 8 * k → q ≤ 8 * k →
      ∀ (A : Type) [Ring A] [Algebra ℝ A],
        HasSchurTable A ((p : ℤ) - q) ↔
        HasSchurTable A (((8 * k - q : ℕ) : ℤ) - (8 * k - p : ℕ))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
