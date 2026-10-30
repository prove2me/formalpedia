-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_transversal_continuous_representation
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.transversal_continuous_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:21:44.698501+00:00
-- url     : https://prove2.me/theorems/c4ed0f79-1a53-412a-b69e-62bec841ca98
-- title:
--   Proposition 15: transversal implementation admits a continuous representation
-- statement:
--   Let $V$ be an isometry from a positive finite-dimensional logical space into a tensor product of finitely many positive finite-dimensional subsystems. Suppose every logical unitary $U$ has a transversal unitary implementation $W$, with $V^\dagger W V=U$. No regularity of these choices is assumed. There exists a continuous representation $u\prime$ on the physical space, each of whose values factorizes into local unitaries, such that $$V^\dagger u\prime(U)V=U,\qquad u\prime(UU\prime)=u\prime(U)u\prime(U\prime).$$ Continuity is asserted for the total map, not for independently selected local factors.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 53, Proposition 15: transversal implementation admits a continuous representation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.53, Proposition 15 (section starts p.52): the original rule need not be continuous
or multiplicative. The conclusion makes the total representation continuous, with pointwise
factorization, and does not assert globally continuous choices of the individual factors. -/
theorem transversal_continuous_representation {d n : ℕ} (c : CovariantErasureCodeData d n)
    (h : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∃ W : Matrix.unitaryGroup (TensorBasis c.dims) ℂ,
        Transversal (W : Matrix (TensorBasis c.dims) (TensorBasis c.dims) ℂ) ∧ c.Vᴴ * (W : Matrix (TensorBasis c.dims) (TensorBasis c.dims) ℂ) * c.V =
          (U : Matrix (Fin d) (Fin d) ℂ)) :
    ∃ r : Matrix.unitaryGroup (Fin d) ℂ →* Matrix.unitaryGroup (TensorBasis c.dims) ℂ,
      Continuous r ∧ ∀ U, Transversal (r U : Matrix (TensorBasis c.dims) (TensorBasis c.dims) ℂ) ∧
        c.Vᴴ * (r U : Matrix (TensorBasis c.dims) (TensorBasis c.dims) ℂ) * c.V = (U : Matrix (Fin d) (Fin d) ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
