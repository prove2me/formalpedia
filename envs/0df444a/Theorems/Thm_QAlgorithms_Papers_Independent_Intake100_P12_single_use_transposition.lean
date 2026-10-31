-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_single_use_transposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.single_use_transposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:07:55.389574+00:00
-- url     : https://prove2.me/theorems/b9cb01ae-8366-4bbb-aba4-c476079f7aae
-- title:
--   One-use exact transpose by the zero Bell outcome
-- statement:
--   For every $d\ge1$, there is a fixed one-slot delayed parallel instrument implementing the zero Bell outcome of the source teleportation construction. For every unknown $U\in U(d)$, its unnormalized success map is
--
--   $$X\longmapsto K_U X K_U^\dagger=\frac1{d^2}U^{\mathsf T}X\overline U,\qquad (K_U)_{ab}=\frac{U_{ba}}d.$$
--
--   Thus the outcome has probability $1/d^2$ on every normalized input, and its normalized output is the transpose channel, including on entangled inputs. This pins both the transpose orientation and Bell-state normalization.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 13, VI A, Eqs. (45)–(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.12–13, Eqs. (45)–(46): the normalized zero-Bell branch gives exact
one-use transposition with constant success probability 1/d^2. -/
theorem single_use_transposition {d : ℕ} (hd : 0 < d) :
    ∃ S F : Op (ProcessBasis (uniformWires d 1)),
      DelayedInstrument (uniformWires d 1) S F ∧
      ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) X,
        taskFromOutputChoi (evaluateOracleSlots S (repeatedChoi 1 U)) X =
          conjSuperop (bellZeroKraus (U : Op (Fin d))) X ∧
        conjSuperop (bellZeroKraus (U : Op (Fin d))) X =
          ((1 / (d : ℝ)^2 : ℝ) : ℂ) •
            conjSuperop ((U : Op (Fin d)).transpose) X := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
