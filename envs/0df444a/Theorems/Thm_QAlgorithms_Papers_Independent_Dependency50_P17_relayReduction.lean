-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P17_relayReduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P17.relayReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:49:20.005742+00:00
-- url     : https://prove2.me/theorems/2f6ede11-7464-4b4c-88a8-b9aae8943f45
-- title:
--   Compute-and-forward message exchange
-- statement:
--   Let $F$ be a finite field and let $M_A,M_B\in F^\ell$ be independent uniform messages on a probability space that also contains all measurement outcomes and link randomness. Let $U$ be the relay's decoded sum, and let $D_A,D_B$ be the sums delivered to Alice and Bob. The terminal reconstructions are $D_A-M_A$ and $D_B-M_B$. Whenever $U=M_A+M_B$ and both downlinks deliver $U$, the reconstructions are respectively $M_B,M_A$. Moreover,
--
--   $$
--   \Pr[D_A-M_A\ne M_B\ \text{or}\ D_B-M_B\ne M_A]
--   \le \Pr[U\ne M_A+M_B]+\Pr[D_A\ne U]+\Pr[D_B\ne U].
--   $$
--
--   Thus reliable computation in the uplink, together with reliable delivery of its result on both downlinks, suffices for message exchange. No independence of the link errors is required.
-- source:
--   Computation-aided classical-quantum multiple access to boost network communication speeds, arXiv:2105.14505v1, PDF p. 5, §II.C.1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.3,5, Section II.C.1: compute-and-forward message exchange.
Alice subtracts her own message from her received sum, and Bob does likewise.
The bound includes uplink error and both downlink errors, so sufficient downlink
reliability is explicit. It applies to every COMP code and every block length. -/
theorem relayReduction {F Omega : Type*} [Field F] [Fintype F]
    [MeasurableSpace F] [MeasurableSingletonClass F] [MeasurableSpace Omega]
    {ell : ℕ} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (a b u da db : Omega → (Fin ell → F))
    (ha : Measurable a) (hb : Measurable b) (hu : Measurable u)
    (hda : Measurable da) (hdb : Measurable db)
    (hmsg : UniformMessagePair mu a b) :
    (∀ w, u w = a w + b w → da w = u w → db w = u w →
      da w - a w = b w ∧ db w - b w = a w) ∧
    mu {w | da w - a w ≠ b w ∨ db w - b w ≠ a w} ≤
      mu {w | u w ≠ a w + b w} + mu {w | da w ≠ u w} + mu {w | db w ≠ u w}
    := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P17

end
