-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_degradation_preserved
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.degradation_preserved
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:35:27.795583+00:00
-- url     : https://prove2.me/theorems/8acb30f7-bb69-4fa6-80cf-c8981d813900
-- title:
--   Degradation and both monotonicities survive synthesis
-- statement:
--   Let $W$ and $V$ be binary-input cq channels with density outputs on finite nonempty registers. Suppose one CPTP map $D$ satisfies $V(x)=D(W(x))$ for both input letters. For $N=2^n$ and each synthesized index $i$, retain the previous classical bits and apply $D^{\otimes N}$ to the quantum outputs. This constructed map $D_{N,i}$ is CPTP and satisfies
--
--   $$
--   V_N^{(i)}(x)=D_{N,i}(W_N^{(i)}(x)),\qquad
--   I(V_N^{(i)})\le I(W_N^{(i)}),\qquad
--   F(W_N^{(i)})\le F(V_N^{(i)}).
--   $$
--
--   Here $I$ is symmetric Holevo information in bits and $F$ is squared Uhlmann fidelity. No commutation or complementary-channel hypothesis is required. This supplies the degradation interface for the polar index sets.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 4, Lemma 3: degradation is preserved by synthesis

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.4, Lemma 3: the constructed degrading map is CPTP, maps both synthesized
letters correctly, and gives both Holevo-information and SQUARED-fidelity inequalities. -/
theorem degradation_preserved {H K : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (W : BinaryCQ H) (V : BinaryCQ K) (hW : IsBinaryCQ W) (hV : IsBinaryCQ V)
    (D : Superop H K) (hD : IsChannel D) (hdeg : ∀ x, V x = D (W x))
    (n : ℕ) (i : Fin (2 ^ n)) :
    IsChannel (synthesizedDegrader D n i) ∧
    (∀ x, synthesized V n i x = synthesizedDegrader D n i (synthesized W n i x)) ∧
    symmetricInformation (synthesized V n i) ≤ symmetricInformation (synthesized W n i) ∧
    squaredFidelity (synthesized W n i false) (synthesized W n i true) ≤
      squaredFidelity (synthesized V n i false) (synthesized V n i true) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
