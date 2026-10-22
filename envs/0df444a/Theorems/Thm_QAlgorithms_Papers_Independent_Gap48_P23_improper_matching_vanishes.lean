-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_improper_matching_vanishes
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.improper_matching_vanishes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:51:17.044125+00:00
-- url     : https://prove2.me/theorems/b1dad253-7ddc-4eac-a30f-2fbd46dfeeb2
-- title:
--   Proposition B.4.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   Construct the diagram from the permutation wires and ordered seed singlet pairings. A matching is improper when a path joins distinct free endpoints on the same side. For every pair of valid weights,
--   $$\text{improper matching}\ \Longrightarrow\ \langle\lambda,w,0|P(\pi)|\mu,v,0\rangle=0.$$
--   In particular the overlap vanishes if $\lambda\ne\mu$. The graph is independent of $w,v$.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 52, Proposition B.4.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.52, Proposition B.4: improper matching annihilates every pair of
seed weights, and distinct partitions always have zero overlap. -/
theorem improper_matching_vanishes (n : ℕ) (hn : 1 ≤ n) (k l : TwoRowShape n)
    (p : Equiv.Perm (Fin n)) (w : Fin (degree n k+1)) (v : Fin (degree n l+1)) :
    (¬ ProperMatching k l p → inner ℂ (schurSeed n k w)
      (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n l v))) = 0) ∧
    (k ≠ l → inner ℂ (schurSeed n k w)
      (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n l v))) = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
