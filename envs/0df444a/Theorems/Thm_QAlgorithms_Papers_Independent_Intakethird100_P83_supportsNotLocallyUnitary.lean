-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_supportsNotLocallyUnitary
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.supportsNotLocallyUnitary
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:14:02.593616+00:00
-- url     : https://prove2.me/theorems/4885b441-4d5b-4c02-822d-60e1df037dba
-- title:
--   The symmetric support is not locally unitarily equivalent to antisymmetric support
-- statement:
--   For the qutrit state $\rho^{(1/2)}$ defined in Proposition 5, let
--
--   $$S_+=\operatorname{span}\{|01\rangle+|10\rangle,|02\rangle+|20\rangle,|12\rangle+|21\rangle\},\quad S_-=\operatorname{span}\{|01\rangle-|10\rangle,|02\rangle-|20\rangle,|12\rangle-|21\rangle\}.$$
--
--   Then $\operatorname{supp}(\rho^{(1/2)})=S_+$, and there are no unitaries $U,V$ on the respective qutrit spaces for which $(U\otimes V)S_+=S_-$. Here $S_+$ is the displayed three-dimensional span. The assertion concerns local unitary equivalence of subspaces.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 4, Unnumbered Remark: symmetric-support example is not locally unitarily equivalent to antisymmetric support

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Remark, PDF p.4: rho(1/2) has exactly the displayed three-dimensional
support, and no tensor product of local unitaries maps it onto S_minus. -/
theorem supportsNotLocallyUnitary :
    supportSpace (rhoAlpha (1/2)) = symmetricSupport ∧
    ¬ ∃ U V : Matrix.unitaryGroup (Fin 3) ℂ,
      Submodule.map (Matrix.toLin' (Matrix.kronecker (U : Matrix (Fin 3) (Fin 3) ℂ)
        (V : Matrix (Fin 3) (Fin 3) ℂ))) symmetricSupport = antisymmetricSupport := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
