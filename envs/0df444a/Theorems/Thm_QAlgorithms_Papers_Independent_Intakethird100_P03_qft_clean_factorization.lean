-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_qft_clean_factorization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.qft_clean_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:02:31.231536+00:00
-- url     : https://prove2.me/theorems/055d0345-62ca-4cb4-a211-f2db712e13bd
-- title:
--   §5 equation (25): ideal clean QFT factorization
-- statement:
--   Let $1\le q\le2^n$, and define the cyclic Fourier vectors with the source's positive sign,
--
--   $$
--   |\psi_{q,a}\rangle=\frac1{\sqrt q}\sum_{b=0}^{q-1}e^{2\pi iab/q}|b\rangle.
--   $$
--
--   Construct $Q_q$ by linear extension of $|\psi_{q,a},0\rangle\mapsto|\psi_{q,a},a\rangle$ and $T_q$ by $|a,0\rangle\mapsto|a,\psi_{q,a}\rangle$. On valid residue inputs with clean work,
--
--   $$
--   V_q[X]\otimes\omega[Y]=Q_q[X,Y]^{-1}T_q[Y,X]\tau_n[Y,X]\tau_n[X,Y].
--   $$
--
--   The equality holds on every superposition of residues $0\le a<q$, including $q=1$ and $n=0,q=1$.
--
--   This is the exact ideal identity; finite approximate implementation is a separate result.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 21, §5 equation (25): ideal clean QFT factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.21, equation (25): exact ideal clean factorization, on the valid input subspace.
Q_q and T_q are constructed above, not arbitrary operators assumed to satisfy the conclusion.
This identity makes no claim of exact finite-gate implementation of approximate measurement. -/
theorem qft_clean_factorization (n q : ℕ) (hq : 0 < q) (hwidth : q ≤ 2 ^ n) :
    ∀ v : EuclideanSpace ℂ (Qubits n),
      (∀ x, q ≤ bitsToNat x → v x = 0) →
      act ((idealQ n q)ᴴ * idealTswapped n q * xorIntoFirst n * xorIntoSecond n)
        (tensorVec v (zeroKet n)) =
        tensorVec (act (cyclicFourierMatrix n q) v) (zeroKet n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
