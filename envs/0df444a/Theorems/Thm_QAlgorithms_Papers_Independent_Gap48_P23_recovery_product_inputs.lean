-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_recovery_product_inputs
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.recovery_product_inputs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:35:29.231665+00:00
-- url     : https://prove2.me/theorems/2939cb63-20f1-4efe-83bd-117e12798c03
-- title:
--   Lemma 3.3.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   The specifically constructed recovery $\Gamma'$ is a unitary-covariant channel and, for all $x,U$,
--   $$(\Gamma'\circ\Gamma\circ\Theta)(\rho_x^U)=\Theta(\rho_x^U).$$
--   Covariance holds on every reduced-space operator.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 23, Lemma 3.3.

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

/-- PDF p.23, Lemma 3.3: the constructed schurRecovery is a covariant channel and
recovers permutation-symmetrized product inputs. -/
theorem recovery_product_inputs (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    IsChannel (schurRecovery alpha) ∧
    (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) rho,
      schurRecovery alpha (conjSuperop (reducedAction n U.val) rho) =
        conjSuperop (tensorPower n U.val) (schurRecovery alpha rho)) ∧
    (∀ (x : Word n 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      schurRecovery alpha (preprocessing alpha (permutationTwirl n (encodedInput U.val x))) =
        permutationTwirl n (encodedInput U.val x)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
