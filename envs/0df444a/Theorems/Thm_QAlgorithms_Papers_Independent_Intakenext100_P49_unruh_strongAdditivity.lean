-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_unruh_strongAdditivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.unruh_strongAdditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:29:03.615991+00:00
-- url     : https://prove2.me/theorems/87b617cd-798b-4930-91ab-64b1d12df428
-- title:
--   Theorem 2: strong Holevo additivity of the full qubit-input Unruh channel
-- statement:
--   Let $0\le z<1$. The one-use Unruh channel has a qubit input and the full countable flagged output
--
--   $$
--   U_z(\rho)=\bigoplus_{\ell=2}^{\infty}p_\ell(z)\,\mathrm{Cl}_{1,\ell-1}(\rho),
--   \qquad p_\ell(z)=(1-z)^3z^{\ell-2}\frac{\ell(\ell-1)}2.
--   $$
--
--   For every CPTP auxiliary channel $T$ between arbitrary positive finite dimensions,
--
--   $$
--   \chi(U_z\otimes T)=\chi(U_z)+\chi(T).
--   $$
--
--   Every Holevo optimization uses arbitrary finite ensembles, including mixed and entangled inputs. The formal statement also establishes nonnegative normalized sector weights, convergence of the output-entropy series for arbitrary normalized block inputs and finite auxiliary inputs, and nonempty bounded optimization sets and regularized rates. These conditions make the infinite-output Holevo quantities genuine finite-entropy quantities. This result concerns the dual-rail qubit-input channel, including $z=0$, and retains all sectors.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 5, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P49

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Support50.P01
  (unruhSectorDilation unruhWeight unruhBlockDilation unruhBlockWeight
   unruhReceiver unruhReceiverEntropy)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.QuditFidelity (depolarizingMap)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Theorem 2: strong additivity of the full countable-output
qubit-input Unruh channel against every positive finite-dimensional auxiliary.
Entropy summability and bounded optimizations are established, not assumed. -/
theorem unruh_strongAdditivity (z : ℝ) (_hz0 : 0 ≤ z) (_hz1 : z < 1) :
    UnruhRegular z ∧
    ∀ a b : ℕ, 0 < a → 0 < b → ∀ T : Superop (Fin a) (Fin b), IsChannel T →
      unruhAuxHolevo z 1 T = unruhHolevo z 1 + holevoCapacity T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
