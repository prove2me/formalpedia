-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_pure_input_restriction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.pure_input_restriction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:01:29.081648+00:00
-- url     : https://prove2.me/theorems/56ad7e83-d3cc-4ad6-877b-9de9256f6114
-- title:
--   Pure-input attainment of channel max-relative entanglement
-- statement:
--   Let $\mathcal N$ be a CPTP channel between nonzero finite-dimensional input and output registers $I$ and $O$. Define its max-relative entropy of entanglement by optimizing the output state quantity over every normalized mixed state on $R\otimes I$, with $R$ of any positive finite dimension. There exists a unit vector $\psi$ on $I\otimes I$ such that
--
--   $$
--   E_{\max}(\mathcal N)=E_{\max}\bigl[(\operatorname{id}_I\otimes\mathcal N)(|\psi\rangle\langle\psi|)\bigr].
--   $$
--
--   Thus a pure input with reference dimension equal to the input dimension attains the original optimization. The original optimization is not defined by imposing this restriction.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 17, §V, after (50): pure-input restriction for channel E_max

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF p.17, after (50): the mixed-input, arbitrary-reference
channel optimization is attained on a pure input whose reference equals the input.
This is a conclusion, not a restriction in channelEMax's definition. -/
theorem pure_input_restriction {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) :
    ∃ psi : EuclideanSpace ℂ (I × I), ‖psi‖ = 1 ∧
      channelEMax N = stateEMax (idTensorSuperop N (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
