-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_stabilizer_lattice
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.stabilizer_lattice
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:48:15.936266+00:00
-- url     : https://prove2.me/theorems/96d4ebb5-70f6-4116-bae3-9290334e6dd2
-- title:
--   §1: finite-index stabilizer and polynomial-size lattice basis
-- statement:
--   Let $k,n>0$, let $M\subseteq\{0,1\}^n$ have unique encodings, let $F$ be a $\mathbb Z^k$ action on $M$, and let $a\in M$. No membership test for $M$ is required, and the black box is unrestricted off $M$. Write $S=\{g:F(g,a)=a\}$. There is a single polynomial $p$ independent of all these data such that
--
--   $$
--   [\mathbb Z^k:S]\le |M|\le 2^n,\qquad S\cong\mathbb Z^k,\qquad \sum_{i=1}^k\operatorname{size}(g_i)\le p(k+n)
--   $$
--
--   for some integer basis $g_1,\ldots,g_k$ of $S$. Size uses a fixed signed binary, self-delimiting coordinate coding. In particular, the index is finite and nonzero.
--
--   This bounds the output size of the stabilizer problem without assuming a basis as input.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 4, §1: finite-index stabilizer and polynomial-size lattice basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF pp.3–4, §1: finite-index, full-rank stabilizer and a polynomial-bit-size basis.
The polynomial precedes every size, action and encoded point. -/
theorem stabilizer_lattice :
    ∃ p : Polynomial ℕ, ∀ (k n : ℕ), 0 < k → 0 < n →
      ∀ (M : Set (Qubits n)) (A : ASPAction k n M) (a : Qubits n) (ha : a ∈ M),
        (stabilizer A a ha).FiniteIndex ∧
        (stabilizer A a ha).index ≤ Nat.card M ∧ Nat.card M ≤ 2 ^ n ∧
        ∃ b : (Fin k → ℤ) ≃+ stabilizer A a ha, latticeBasisBits b ≤ p.eval (n + k) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
