-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_optimumEncodingSDP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.optimumEncodingSDP
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:24:08.304969+00:00
-- url     : https://prove2.me/theorems/60cf5f8a-7786-4cb3-9340-dfa9f536ab75
-- title:
--   Fixed-noise fixed-recovery encoding is an attained SDP
-- statement:
--   Let $H=\mathbb C^h$, $K=\mathbb C^k$, $0<h<k$, and fix a density $\rho$ on $H$ and any normalized finite-reference purification. Fix CPTP noise $\mathcal E:K\to K$ with Kraus family $E_j$ and CPTP recovery $\mathcal D:K\to H$ with Kraus family $D_i$. Optimize over every CPTP encoder $\mathcal V:H\to K$. Define
--
--   $$
--   C_{\mathrm{enc}}=\sum_{i,j}|(D_iE_j)^\dagger\rho\rangle\rangle\langle\langle(D_iE_j)^\dagger\rho|.
--   $$
--
--   The encoder Choi matrix acts on $K\otimes H$ and satisfies
--
--   $$
--   \max_{\mathcal V\;\mathrm{CPTP}}F_e(\rho,\mathcal D\circ\mathcal E\circ\mathcal V)
--   =\max_{X\succeq0,\;\operatorname{tr}_KX=I_H}\operatorname{tr}(XC_{\mathrm{enc}}).
--   $$
--
--   Both maxima are attained, every encoder has this objective, and every feasible matrix corresponds to an encoder. The coefficient is the algebraic expansion of (16), not a displayed formula on p.7. This expresses the source's same-process claim without restricting encoders to isometries or claiming convergence of alternating optimization.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 7, VI C: optimum encoding for fixed recovery is also an SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.7, §VI C: for fixed noise and recovery, optimization over all CPTP encoders
is also an attained SDP. The displayed coefficient here expands (16); it is not
printed on p.7. No convergence or joint optimality of alternating optimization is asserted. -/
theorem optimumEncodingSDP {h k a m n : ℕ} (hh : 0 < h) (hk : 0 < k) (hspread : h < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : IsKrausFamily E)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (hD : IsKrausFamily D) :
    (∀ V : Superop (Fin h) (Fin k), IsChannel V →
      ChoiFeasible (outputFirstChoi V) ∧
      purificationFidelity psi (krausApply D ∘ krausApply E ∘ V) =
        (outputFirstChoi V * encodingCoefficient rho E D).trace.re) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ, ChoiFeasible X →
      ∃ V : Superop (Fin h) (Fin k), IsChannel V ∧ outputFirstChoi V = X) ∧
    ∃ (V : Superop (Fin h) (Fin k))
      (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ),
      IsChannel V ∧ outputFirstChoi V = X ∧ ChoiFeasible X ∧
      purificationFidelity psi (krausApply D ∘ krausApply E ∘ V) =
        (X * encodingCoefficient rho E D).trace.re ∧
      (∀ Y, ChoiFeasible Y → (Y * encodingCoefficient rho E D).trace.re ≤
        (X * encodingCoefficient rho E D).trace.re) ∧
      (∀ W : Superop (Fin h) (Fin k), IsChannel W →
        purificationFidelity psi (krausApply D ∘ krausApply E ∘ W) ≤
          purificationFidelity psi (krausApply D ∘ krausApply E ∘ V)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
