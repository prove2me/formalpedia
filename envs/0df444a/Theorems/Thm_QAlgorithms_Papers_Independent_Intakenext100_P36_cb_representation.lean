-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_cb_representation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.cb_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:14:17.82475+00:00
-- url     : https://prove2.me/theorems/35bbb721-56ae-48f3-85bb-b2a3659f429f
-- title:
--   Theorem 19: an attained generalized Choi–Kraus factorization
-- statement:
--   Let $n,k\ge1$ and let $\phi:M_n\to M_k$ be complex-linear. There exist an integer $m\le nk$ and matrices $A_i\in M_{k,n}$ and $B_i\in M_{n,k}$ such that, for every $X\in M_n$,
--
--   $$\phi(X)=\sum_{i=1}^m A_iXB_i,\qquad \|\phi\|_{\rm cb}^2=\|\phi^\dagger\|_\diamond^2=\left\|\sum_i A_iA_i^\dagger\right\|\left\|\sum_iB_i^\dagger B_i\right\|.$$
--
--   The map $\phi^\dagger:M_k\to M_n$ is defined by the bilinear trace identity $\operatorname{Tr}(\phi(X)Y)=\operatorname{Tr}(X\phi^\dagger(Y))$. Matrix norms are Euclidean operator norms; the diamond norm uses an input-dimension ancilla and unnormalized trace norm. Neither Kraus normalization nor positivity is assumed. An empty representation is allowed for the zero map.
--
--   This finite structural consequence of generalized Stinespring supplies an attained objective for the norm computation; an arbitrary supplied representation is not asserted to attain it.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 8, Theorem 19 (CB Representation Theorem)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- Theorem 19, PDF p.8: an attained finite factorization with at most nk terms.
The representation is existential; an arbitrary supplied representation need not attain.
This concrete consequence of generalized Stinespring is used by the paper's algorithm. -/
theorem cb_representation {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (phi : Map n k) :
    ∃ m : ℕ, m ≤ n * k ∧
      ∃ A : Fin m → Matrix (Fin k) (Fin n) ℂ,
      ∃ B : Fin m → Matrix (Fin n) (Fin k) ℂ,
        IsGeneralizedChoiKraus phi A B ∧
        extendedCBNorm phi ^ 2 = rectangularDiamondNorm (traceDual phi) ^ 2 ∧
        rectangularDiamondNorm (traceDual phi) ^ 2 =
          ENNReal.ofReal (specNorm (∑ i, A i * (A i)ᴴ) *
            specNorm (∑ i, (B i)ᴴ * B i)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end
