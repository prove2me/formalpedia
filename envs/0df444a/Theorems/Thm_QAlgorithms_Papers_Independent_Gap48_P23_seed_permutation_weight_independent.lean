-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_seed_permutation_weight_independent
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.seed_permutation_weight_independent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:49:53.268226+00:00
-- url     : https://prove2.me/theorems/b0369662-9e7c-472d-807a-f832f081dcdc
-- title:
--   Proposition B.2.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For fixed $\lambda$ and permutation $\pi$, the seed overlap is independent of weight:
--   $$\langle\lambda,w,0|P(\pi)|\lambda,w,0\rangle=\langle\lambda,v,0|P(\pi)|\lambda,v,0\rangle.$$
--   Both weights range over $0,\ldots,m_\lambda-1$.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 50, Proposition B.2.

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

/-- PDF p.50, Proposition B.2: seed self-overlap is independent of booleanWordWeight. -/
theorem seed_permutation_weight_independent (n : ℕ) (hn : 1 ≤ n)
    (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) (w v : Fin (degree n k + 1)) :
    inner ℂ (schurSeed n k w) (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k w))) =
    inner ℂ (schurSeed n k v) (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k v))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
