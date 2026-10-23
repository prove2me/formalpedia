-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_common_dilation_convex_roof
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.common_dilation_convex_roof
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:12:53.633054+00:00
-- url     : https://prove2.me/theorems/29525a10-ab22-4868-8877-e96bfaf6287a
-- title:
--   Unnumbered identity (26): common dilation convex roof and constrained Holevo difference
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $V^\dagger V=I$ and let $\rho$ be a density matrix. Write $\Phi,\Phi^C$ for the two marginal channels and $\gamma=V\rho V^\dagger$. Let $E_F$ be the convex roof of marginal entropy, and $\chi(\Phi,\rho)=S(\Phi(\rho))-\widehat S_\Phi(\rho)$, where $\widehat S_\Phi$ is the convex roof over finite normalized pure input decompositions of the same $\rho$. Then
--
--   $$
--   E_F(\gamma)=S(\Phi(\rho))-\chi(\Phi,\rho)=S(\Phi^C(\rho))-\chi(\Phi^C,\rho).
--   $$
--
--   This is the constrained Holevo identity for one common dilation; it does not equate unconstrained conjugate capacities.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 12, Unnumbered identity (26): common dilation convex roof and constrained Holevo difference

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Unnumbered identity (26), PDF p.12: the SAME rho and the common dilation.
Only constrained Holevo differences are equated, not unconstrained capacities. -/
theorem common_dilation_convex_roof [Nonempty A] [Nonempty B] [Nonempty C]
    (V : Matrix (B × C) A ℂ) (hV : Vᴴ * V = 1)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    entanglementFormation (V * rho * Vᴴ) =
      entropy (receiverChannel V rho) - constrainedHolevo (receiverChannel V) rho ∧
    entanglementFormation (V * rho * Vᴴ) =
      entropy (complementaryChannel V rho) - constrainedHolevo (complementaryChannel V) rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
