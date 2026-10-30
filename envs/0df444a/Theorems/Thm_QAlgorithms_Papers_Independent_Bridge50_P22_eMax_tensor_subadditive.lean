-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_eMax_tensor_subadditive
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.eMax_tensor_subadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:18:20.613164+00:00
-- url     : https://prove2.me/theorems/666ff8e7-275f-4bd4-adcf-a621dbd5e2c5
-- title:
--   Subadditivity of channel max-relative entanglement
-- statement:
--   Let $\mathcal N_{A\to B}$ and $\mathcal M_{C\to D}$ be quantum channels on positive finite-dimensional complex registers. For each channel, let $E_{\max}$ denote the supremum of the output max-relative entropy of entanglement, in bits, over all unit pure inputs with a reference isomorphic to the channel input. Then
--
--   $$E_{\max}(\mathcal N\otimes\mathcal M)\le E_{\max}(\mathcal N)+E_{\max}(\mathcal M).$$
--
--   The tensor-product channel acts on arbitrary joint inputs, including inputs entangled across $A$ and $C$. The result asserts subadditivity; equality is explicitly left open in the source.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 16, Section 5 / eq. (94)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section Statements

variable {A B C D L R : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq L] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

/-- PDF p.16, (94): channel Emax is subadditive, not asserted additive.
The accepted tensorAction is defined on every matrix unit, so channelEMax
optimizes all pure inputs across the joint reference and both channel inputs. -/
theorem eMax_tensor_subadditive (N : Superop A B) (hN : IsChannel N)
    (M : Superop C D) (hM : IsChannel M) :
    channelEMax (tensorAction N M) ≤ channelEMax N + channelEMax M := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
