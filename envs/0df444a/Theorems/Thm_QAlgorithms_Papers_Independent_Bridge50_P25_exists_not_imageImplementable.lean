-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_exists_not_imageImplementable
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.exists_not_imageImplementable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:13:41.215991+00:00
-- url     : https://prove2.me/theorems/e034d11f-a4e7-44b6-a946-8b0bdfc31ad7
-- title:
--   Theorem A.2: channel not implementable from its image
-- statement:
--   There exist positive finite dimensions $d_A,d_B$ and a quantum channel $T:M_{d_A}\to M_{d_B}$ such that, for every positive finite reference dimension, there are no normalized state $\sigma_{A''A'}$ with $d_{A'}=d_A$ and two-party LOCC operation $\Lambda$ satisfying
--
--   $$T(\rho_A)=\Lambda\!\left(\rho_A\otimes(\mathrm{id}_{A''}\otimes T)(\sigma_{A''A'})\right)\quad\text{for every density matrix }\rho_A.$$
--
--   The operation acts across $AA'':B'$ and outputs only Bob's system. The resource is prepared with a single use of $T$.
--
--   This rules out image implementability for some channels. It does not rule out simulation from a resource prepared using multiple channel uses. Proof-only numerical and zero-probability corrections are recorded in the moderation notes.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 26, Theorem A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem A.2, PDF pp.26--29: failure of every single-use image implementation,
with arbitrary finite reference and LOCC. Multiple-use resource preparation is
not excluded. Printed proof p.27: n*(log2(sqrt(4/3))-1/2)>=n/2, whose left slope is negative.
Changed: c=log2(sqrt(4/3))>0 and epsilon=c/2 in (A3) give ER(tau0)>=n*c/2.
Why: a positive linear slope suffices for separation. Printed p.28 (A13) assigns
zero to a zero-probability conditional state; replace it by any normalized state.
These are proof-only corrections; independent moderation remains required. -/
theorem exists_not_imageImplementable :
    ∃ a b : ℕ, ∃ T : Superop (Fin (a + 1)) (Fin (b + 1)), IsChannel T ∧
      ∀ r : ℕ, ∀ sigma : Mat (Fin (r + 1) × Fin (a + 1)),
      ∀ L : Superop ((Fin (a + 1) × Fin (r + 1)) × Fin (b + 1)) (Unit × Fin (b + 1)),
        ¬ ImplementsFrom T sigma L := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
