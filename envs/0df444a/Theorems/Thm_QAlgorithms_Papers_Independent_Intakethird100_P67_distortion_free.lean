-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_distortion_free
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.distortion_free
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:54:27.599201+00:00
-- url     : https://prove2.me/theorems/80d336c2-dcd9-4df9-9b53-446e2b9defa1
-- title:
--   §III A, Eq.(21): distortion-free factorization
-- statement:
--   Fix normalized pure samples generating the full supported algebra, an anchor, $K\ge2$, and $T\ge0$. Construct $\mathcal E_I$ by the same Appendix-A emulator with target equal to the identity. For every ambient unitary $U$ and input density operator $\rho$,
--
--   $$\mathcal E_U(\rho)=U\mathcal E_I(\rho)U^\dagger.$$
--
--   Thus the distortion channel is fixed by the input samples before $U$ is chosen. It is the constructed main-system channel, rather than an arbitrary channel selected afterward or the outcome-dependent discarded SWAP wire.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 6, §III A, Eq.(21): distortion-free factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.6, Eq.(21): factorization through the constructed target-I channel. -/
theorem distortion_free (phi : K → EuclideanSpace ℂ I) (a : K) (hK : 2 ≤ Fintype.card K)
    (hphi : ∀ k, IsState (phi k)) (hgen : Generates (pureSamples phi)) (T : ℕ) :
    ∀ U : Matrix.unitaryGroup I ℂ, ∀ rho : Matrix I I ℂ, IsDensityMatrix rho →
      emulate phi a (U : Matrix I I ℂ) T rho = densityConjugation (U : Matrix I I ℂ) (emulate phi a 1 T rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
