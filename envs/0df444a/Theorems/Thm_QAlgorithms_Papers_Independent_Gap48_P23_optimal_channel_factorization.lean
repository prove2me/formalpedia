-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_optimal_channel_factorization
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.optimal_channel_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:38:15.173598+00:00
-- url     : https://prove2.me/theorems/8aa842b3-3d98-4931-93f1-e4d35569cebb
-- title:
--   Corollary 3.6.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For every symmetric equivariant Boolean function on a positive odd number of inputs there is a covariant reduced-space channel $\Phi'$ such that
--   $$F_f(\Phi'\circ\Gamma)=F_f.$$
--   The full channel is unitary-equivariant.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 25, Corollary 3.6.

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

/-- PDF p.25, Corollary 3.6: optimal computation factors through generic preprocessing. -/
theorem optimal_channel_factorization (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (f : Word n 2 → Fin 2) (hf : WordSymmetric f) (he : Equivariant f) :
    ∃ Psi : Superop (ReducedIndex n) (Fin 2), IsChannel Psi ∧
      (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) rho,
        Psi (conjSuperop (reducedAction n U.val) rho) = conjSuperop U.val (Psi rho)) ∧
      IsFunctionOptimal (fun _ => True) f (Psi ∘ preprocessing alpha) ∧
      WordUnitaryEquivariant (Psi ∘ preprocessing alpha) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
