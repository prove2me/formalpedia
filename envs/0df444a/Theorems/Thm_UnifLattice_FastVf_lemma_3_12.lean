-- Prove2me | Theorems.Thm_UnifLattice_FastVf_lemma_3_12
-- name    : UnifLattice.FastVf.lemma_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:20:56.319106+00:00
-- url     : https://prove2.me/theorems/fab56b69-9acc-4366-ace2-7791c229c646
-- title:
--   Lemma 3.12 — linearization vec((I_m ⊗ vec A)BC) = M̂(vec A ⊗ vec B ⊗ vec C), M̂ computable in time poly(m)
-- statement:
--   **Lemma 3.12 (Linearization).** For all $m\in\mathbb N$ there is a matrix $\widehat M\in\mathbb Z^{m^4\times m^6}$ such that for all $A,B,C\in\mathbb Z^{m\times m}$
--   $$\mathrm{vec}\big((I_m\otimes\mathrm{vec}(A))BC\big)=\widehat M\,\big(\mathrm{vec}(A)\otimes\mathrm{vec}(B)\otimes\mathrm{vec}(C)\big),\tag{3.9}$$
--   and $\widehat M$ can be computed in time $\mathrm{poly}(m)$. Here $\mathrm{vec}$ stacks columns and $\otimes$ is the Kronecker product.
--
--   In the proof of Theorem 3.13 it turns $V_f$ into $\mathrm{vec}(V_f)=\widehat Mv_g$, replacing the trilinear expression by a linear one.
--
--   **Formalization Note.** The statement asserts one polynomial-time algorithm (`PolyTimeComputable`) that maps $m$, written in unary, to the code of a matrix $\widehat M$ satisfying (3.9) for all integer $A,B,C$.
--
--   Differences from the source:
--   - encoding: M̂ can be computed in time poly(m) → one function alg with QAlgorithms.Complexity.PolyTimeComputable alg and alg (encNat m) = encMhat M̂, m in unary; reason: the input length is m + 1, so time polynomial in the input length is poly(m); multi-stack Turing machines and the paper's algorithms simulate each other with polynomial overhead
--   - encoding: vec, ⊗ on Z^{m×m}, M̂ ∈ Z^{m^4×m^6} → vectors on product index types (Matrix.vec indexed by (column, row), kron indexed by pairs), M̂ : Matrix (Fin m × (Fin m × (Fin m × Fin m))) (K6 m) ℤ; reason: the lexicographic flattening of these index types is the paper's flattening
--   - generalization: m ∈ ℕ (lattice parameter) → every m : ℕ, including m = 0 (all matrices empty); reason: the m = 0 instances are trivially true; every instance of the source is covered
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 24, Lemma 3.12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_QuadraticCommitment
import Definitions.Def_UnifLattice_FastVf_Encoding

open Matrix

namespace UnifLattice.FastVf

/-- Lemma 3.12 (Linearization), p. 24: for all `m`, there is `M̂ ∈ ℤ^{m⁴ × m⁶}` with
`vec((I_m ⊗ vec(A)) B C) = M̂ (vec(A) ⊗ vec(B) ⊗ vec(C))` for all `A, B, C ∈ ℤ^{m×m}` (Eq. (3.9)),
and `M̂` can be computed in time `poly(m)`: one polynomial-time algorithm maps `m` (in unary) to the
code of such an `M̂`. -/
theorem lemma_3_12 :
    ∃ alg : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable alg ∧
      ∀ m : ℕ, ∃ Mhat : Matrix (Fin m × (Fin m × (Fin m × Fin m))) (K6 m) ℤ,
        alg (QAlgorithms.Complexity.encNat m) = encMhat Mhat ∧
        ∀ A B C : Matrix (Fin m) (Fin m) ℤ,
          vec (kronVecI A * B * C) = Mhat *ᵥ kron (kron (vec A) (vec B)) (vec C) := by sorry

end UnifLattice.FastVf
