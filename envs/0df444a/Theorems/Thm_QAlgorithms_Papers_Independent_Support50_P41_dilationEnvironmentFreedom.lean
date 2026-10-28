-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_dilationEnvironmentFreedom
-- name    : QAlgorithms.Papers.Independent.Support50.P41.dilationEnvironmentFreedom
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:36:38.523987+00:00
-- url     : https://prove2.me/theorems/eed93037-054b-4bef-b30c-c8f50458f54f
-- title:
--   §A.4: environment-unitary freedom of dilations
-- statement:
--   Suppose $U,\eta$ and $V,\zeta$ are two pure-environment unitary representations of the same channel on a nonzero finite-dimensional system, using the same nonzero finite environment. Both initial environment vectors are unit vectors. Then there exists a single unitary $W$ on that environment such that, for every system vector $v$,
--
--   $$V(v\otimes\zeta)=(I\otimes W)U(v\otimes\eta).$$
--
--   This describes the freedom on the used input subspace. Representations with different environment sizes can first be padded to a common size.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 36, §A.4: environment-unitary freedom of dilations

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF p.36: common-environment dilations differ by a post-interaction environment unitary on the used input subspace. -/
theorem dilationEnvironmentFreedom {d e : ℕ} [NeZero d] [NeZero e]
    (U V : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (eta zeta : EuclideanSpace ℂ (Fin e)) (heta : IsState eta) (hzeta : IsState zeta)
    (hsame : ∀ X, dilationChannel U eta X = dilationChannel V zeta X) :
    ∃ W : Matrix.unitaryGroup (Fin e) ℂ,
      ∀ v : EuclideanSpace ℂ (Fin d),
        act (V : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
          (WithLp.toLp 2 fun p => v p.1 * zeta p.2) =
        act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ)
          (W : Matrix (Fin e) (Fin e) ℂ))
          (act (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
            (WithLp.toLp 2 fun p => v p.1 * eta p.2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
