-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_tensor_properties
-- name    : QAlgorithms.Nannicini.tensor_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:39.73823+00:00
-- url     : https://prove2.me/theorems/7f1607cc-f6db-4e69-8fa7-ac087f39f35a
-- title:
--   Algebraic properties of the tensor (Kronecker) product
-- statement:
--   Let $m,n\ge 0$ be integers, let $A,B\in\mathbb C^{m\times m}$ and $C,D\in\mathbb C^{n\times n}$, let $u,v\in\mathbb C^m$, $w,x\in\mathbb C^n$, and $a,b\in\mathbb C$. Here $\otimes$ is the Kronecker product, which is the tensor product with respect to the standard bases, and $M^\dagger=\overline{M}^{\top}$ is the conjugate transpose. Then:
--
--   1. $(A\otimes C)(B\otimes D)=AB\otimes CD$;
--   2. $(A\otimes C)(u\otimes w)=Au\otimes Cw$;
--   3. $(u+v)\otimes w=u\otimes w+v\otimes w$;
--   4. $u\otimes(w+x)=u\otimes w+u\otimes x$;
--   5. $(au)\otimes(bw)=ab\,(u\otimes w)$;
--   6. $$(A\otimes C)^\dagger=A^\dagger\otimes C^\dagger.$$
--
--   These identities are the basic calculus of multi-register states and of operators acting on separate registers, and they are used throughout the analysis of quantum circuits.
--
--   **Formalization Note** The vector space $\mathbb C^m\otimes\mathbb C^n$ is indexed by pairs $(i,k)\in\{0,\dots,m-1\}\times\{0,\dots,n-1\}$ in lexicographic order, which is exactly the block order of the Kronecker product. The source types $A,B$ as "$A, B : \mathbb C^{m\times m}$", a typo for $A,B\in\mathbb C^{m\times m}$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 9, Proposition 1.4. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.9, Proposition 1.4: algebraic properties of the tensor (Kronecker) product.
For `A, B ∈ ℂ^{m×m}`, `C, D ∈ ℂ^{n×n}`, `u, v ∈ ℂ^m`, `w, x ∈ ℂ^n`, `a, b ∈ ℂ`:
(i) `(A ⊗ C)(B ⊗ D) = AB ⊗ CD`; (ii) `(A ⊗ C)(u ⊗ w) = Au ⊗ Cw`;
(iii) `(u + v) ⊗ w = u ⊗ w + v ⊗ w`; (iv) `u ⊗ (w + x) = u ⊗ w + u ⊗ x`;
(v) `(au) ⊗ (bw) = ab (u ⊗ w)`; (vi) `(A ⊗ C)† = A† ⊗ C†`. -/
theorem tensor_properties {m n : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (C D : Matrix (Fin n) (Fin n) ℂ) (u v : EuclideanSpace ℂ (Fin m))
    (w x : EuclideanSpace ℂ (Fin n)) (a b : ℂ) :
    Matrix.kronecker A C * Matrix.kronecker B D = Matrix.kronecker (A * B) (C * D) ∧
    act (Matrix.kronecker A C) (tensorVec u w) = tensorVec (act A u) (act C w) ∧
    tensorVec (u + v) w = tensorVec u w + tensorVec v w ∧
    tensorVec u (w + x) = tensorVec u w + tensorVec u x ∧
    tensorVec (a • u) (b • w) = (a * b) • tensorVec u w ∧
    (Matrix.kronecker A C).conjTranspose =
      Matrix.kronecker A.conjTranspose C.conjTranspose := by
  sorry





end QAlgorithms.Nannicini
