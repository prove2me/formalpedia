-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_noiseRecoveryChoi
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.noiseRecoveryChoi
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:21:02.980757+00:00
-- url     : https://prove2.me/theorems/578f0845-01d4-42f8-b92a-fc2078edd5eb
-- title:
--   Choi operator of noise followed by recovery
-- statement:
--   Let $H=\mathbb C^h$ and $K=\mathbb C^k$, $h,k>0$. Let CPTP noise $\mathcal E:L(H)\to L(K)$ and recovery $\mathcal R:L(K)\to L(H)$ have finite normalized Kraus families $E_j$ and $R_i$. With $X_R$ acting on $H\otimes K$, the composite has Choi matrix on $H\otimes H$ given by
--
--   $$
--   X_{\mathcal R\circ\mathcal E}
--   =\sum_{i,j}|R_iE_j\rangle\rangle\langle\langle R_iE_j|
--   =\sum_j(I_H\otimes E_j^T)X_R(I_H\otimes E_j^*).
--   $$
--
--   The symbol $*$ denotes entrywise conjugation without transposition. This formula preserves the unnormalized output-first convention when composing noise and recovery.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 3, IV, Eqs. (18)-(19): Choi operator of noise followed by recovery

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF pp.3–4, (18)–(19): Choi composition for noise followed by recovery. -/
theorem noiseRecoveryChoi {h k m n : ℕ} (hh : 0 < h) (hk : 0 < k)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (hE : IsKrausFamily E)
    (R : Fin n → Matrix (Fin h) (Fin k) ℂ) (hR : IsKrausFamily R) :
    outputFirstChoi (krausApply R ∘ krausApply E) =
      ∑ i, ∑ j, dyad (operatorKet (R i * E j)) (operatorKet (R i * E j)) ∧
    outputFirstChoi (krausApply R ∘ krausApply E) =
      ∑ j, Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (E j)ᵀ * krausChoi R *
        Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) ((E j).map (fun z => conj z)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
