-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_pptKey_nonzeroVolume_fourByFour
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.pptKey_nonzeroVolume_fourByFour
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:24:31.417449+00:00
-- url     : https://prove2.me/theorems/dfa34649-5bc0-4562-b564-c72893ee7e41
-- title:
--   Observation 3: nonzero volume of PPT key-distillable states in 4⊗4
-- statement:
--   Let $\rho_H$ denote the physical $4\otimes4$ Hadamard resource and let $\|\cdot\|_2$ denote the Hilbert–Schmidt norm. There exist $q\in(0,1)$ and $\varepsilon>0$ such that every Hermitian trace-one matrix $\sigma$ satisfying
--
--   $$\left\|\sigma-\left(q\rho_H+(1-q)I_{16}/16\right)\right\|_2<\varepsilon$$
--
--   is a density matrix, is PPT across Alice and Bob, and has $K_D(\sigma)>0$. This full-dimensional open ball in the real affine space of Hermitian trace-one matrices witnesses nonzero volume of PPT key-distillable states. The noisy center, with signal weight sufficiently close to one, corrects the printed proof's center and direction of noise. The conclusion concerns all PPT key states, not the low-parameter exact family $\rho_U$.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 3, Observation 3: nonzero volume of PPT key-distillable states in 4⊗4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.3, Observation 3: a full-dimensional affine ball of PPT key states.
Correction: its center is q rho_H+(1-q)I/16, with q<1 close to ONE, not rho_H.
The set is all PPT key states; the exact low-parameter rho_U family is not full-volume.
The affine ball explicitly witnesses nonzero volume. -/
theorem pptKey_nonzeroVolume_fourByFour :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : Op (Fin 4 × Fin 4), sigma.IsHermitian → sigma.trace = 1 →
        squaredDistance sigma
          ((q : ℂ) • physicalFin rhoHadamard + (((1-q)/16 : ℝ) : ℂ) • 1) < eps^2 →
        IsPPTWithKey sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
