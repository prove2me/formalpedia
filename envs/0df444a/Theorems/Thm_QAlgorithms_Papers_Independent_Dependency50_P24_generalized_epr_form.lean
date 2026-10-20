-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_generalized_epr_form
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.generalized_epr_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:22:47.221972+00:00
-- url     : https://prove2.me/theorems/d9e802c1-1afa-44cc-93f3-07b8791466ad
-- title:
--   §IV: generalized EPR operator amplitudes
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   An operator $\gamma$ on a $d$-by-$d$ key and finite shield is a private dit if and only if some shield state $\sigma$ and shield unitaries $U_i$ give
--
--   $$\gamma=\Psi\Psi^\dagger,\qquad\Psi=\frac1{\sqrt d}\sum_i|ii\rangle\otimes Y_i,\qquad Y_i=U_i\sqrt\sigma.$$
--
--   The rectangular operator $\Psi$ maps the shield into key times shield. The common normalized polar modulus is essential; for $d=2$ its corner block is $Y_0Y_1^\dagger/2$. This is the generalized EPR representation.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 9, §IV: generalized EPR operator amplitudes

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.9, Eqs.(39)–(42): generalized EPR form with a common normalized polar modulus.
The actual private-bit corner is one half of Y0 Y1†. -/
theorem generalized_epr_form {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T] (gamma : Op (Key d × (S × T))) :
    IsPrivate gamma ↔ ∃ tau : Op (S × T), IsDensityMatrix tau ∧
      ∃ U : Fin d → Matrix.unitaryGroup (S × T) ℂ,
        gamma = operatorAmplitude tau U * (operatorAmplitude tau U)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
