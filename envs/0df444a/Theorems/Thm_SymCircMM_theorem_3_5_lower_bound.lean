-- Prove2me | Theorems.Thm_SymCircMM_theorem_3_5_lower_bound
-- name    : SymCircMM.theorem_3_5_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:59.104027+00:00
-- url     : https://prove2.me/theorems/0910e710-c3de-4447-aa5b-4ec2cbf1f2d0
-- title:
--   Theorem 3.5 — every $G$-symmetric circuit for $\mathrm{MM}_n$ has size at least $n^2N/2$
-- statement:
--   Let $G\le S_n$ with $\mathrm{char}(F)\nmid|G|$, let $\lambda_1V_1\oplus\cdots\oplus\lambda_rV_r$ be a decomposition of the permutation representation of $G$ over $F$ into irreducibles with $V_i\not\simeq V_j$ for $i\ne j$, and let $N=\sum_{i=1}^r\dim V_i$. Then every $G$-symmetric algebraic circuit $C$ computing $\mathrm{MM}_n$ satisfies
--
--   $$\mathrm{size}(C)\ \ge\ \frac{n^2N}{2};$$
--
--   in particular its size is $\Omega(n^2N)$.
--
--   All the lower bounds of the paper are instances of this theorem; $N=n$ exactly when the permutation representation is multiplicity free.
--
--   **Formalization Note** The bound is written $n^2N\le2\,\mathrm{size}(C)$, which implies the $\Omega$ clause.
--
--   Differences from the source:
--
--   - encoding: the index set [n] = {1, …, n} → a finite type ι with n = card ι; reason: a relabelling of the index set
--   - encoding: an algebraic circuit (a finite labelled multi-DAG with designated output gates) and the polynomial ĝ ∈ F[X] of each gate → Circuit F X γ on a finite gate type γ (labels, edge multiplicities wire g c, a rank function for acyclicity); gate values in MvPolynomial X F; the output gates given by a map out : ι × ι → γ; reason: the same objects; "computing MM_n" is equality of polynomials at the designated output gates
--   - generalization: a G-symmetric circuit (Definition 2.2): one input gate per variable, and σ̂ permutes (by Remark 2.4, fixes) the output gates → IsGSymmetric: for each σ ∈ G some bijection of the gates preserving edge multiplicities and labels, variables renamed by (2); input labels may repeat and nothing is required of the output gates; reason: every circuit symmetric in the paper's sense is symmetric in this sense, so the lower bound covers more circuits; the proof passes to the rigidified circuit of Proposition 4.2, where the extension is unique, and never uses the output condition
--   - generalization: N = ∑_i dim V_i over the pairwise inequivalent constituents V_1, …, V_r of a decomposition λ_1V_1 ⊕ ⋯ ⊕ λ_rV_r of the permutation representation → ∑_s finrank W_s over any family W of pairwise inequivalent irreducible subrepresentations of the permutation representation; reason: one copy of each V_i inside the decomposition is such a family and gives the paper's N; every such family has sum at most N
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
--   - encoding: size at least n²N/2; in particular Ω(n²·N) → n² · N ≤ 2 · size; reason: the same inequality without division; the Ω clause follows with constant 1/2
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Theorem 3.5, p.9 (PDF p.10); proof p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SymCircMM_Circuit_IsGSymmetric
import Definitions.Def_SymCircMM_permRep

set_option autoImplicit false

namespace SymCircMM

/-- **Theorem 3.5** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.9 (PDF p.10); proof p.13 (PDF p.14)): "Let G ≤ S_n with char(F) ∤ |G|, and
let λ_1V_1 ⊕ λ_2V_2 ⊕ ⋯ ⊕ λ_rV_r be a decomposition into irreps of the permutation representation of G
over F, such that if i ≠ j, V_i and V_j are not equivalent, and let N = ∑^r_{i=1} dim(V_i). Then, any
G-symmetric algebraic circuit for MM_n has size at least n²N/2; in particular it has size Ω(n²·N)."

**Formalization Note.** The `V_i` are any family `W` of pairwise inequivalent irreducible
subrepresentations of the permutation representation (one copy of each constituent of a decomposition
is such a family, and conversely every such family has `∑ dim ≤ N`). "Size at least `n²N/2`" is
`n² N ≤ 2 · size`, which gives the `Ω` clause. -/
theorem theorem_3_5_lower_bound {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (Equiv.Perm ι)) (hG : (Nat.card G : F) ≠ 0)
    {r : ℕ} (W : Fin r → Subrepresentation (permRep F G))
    (hW : ∀ s, (W s).toRepresentation.IsIrreducible)
    (hWW : ∀ s t, s ≠ t → IsEmpty ((W s).toRepresentation.Equiv (W t).toRepresentation))
    {γ : Type} [Fintype γ] (C : Circuit F (MMVar ι) γ) (hC : C.IsGSymmetric G)
    (hMM : C.ComputesMM) :
    Fintype.card ι ^ 2 * ∑ s, Module.finrank F (W s).toSubmodule ≤ 2 * C.size := by sorry

end SymCircMM
