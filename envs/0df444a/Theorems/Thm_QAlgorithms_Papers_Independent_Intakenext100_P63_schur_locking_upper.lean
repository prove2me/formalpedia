-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_schur_locking_upper
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.schur_locking_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:13:20.823907+00:00
-- url     : https://prove2.me/theorems/b271920b-5685-40c4-bd4a-1d4833e6f91e
-- title:
--   Accessible equivocation bounds weak locking capacity from above
-- statement:
--   Let $A,B,E$ be nonzero finite-dimensional Hilbert spaces, and let $V:A\to B\otimes E$ be a normalized Stinespring isometry defining receiver channel $\mathcal N$ and complementary channel $\mathcal N^c$. Suppose that, in the specified computational basis of $A$,
--   $\mathcal N^c(|i\rangle\langle j|)=\delta_{ij}\rho_i$, where every $\rho_i$ is a normalized density matrix on $E$. For a probability vector $p$, define $S_{\rm acc}(p;\rho)=\min_Q H(I|J)$ using the joint law $\Pr(I=i,J=j)=p_i\operatorname{Tr}(\rho_iQ_j)$, with $Q$ ranging over all finite POVMs. Then
--
--   $$L_W(\mathcal N)\le\max_p S_{\rm acc}(p;\rho).$$
--
--   All entropies are in bits. The operational capacity uses uniform messages, an independent uniform secret of $o(n)$ bits, and vanishing averaged reliability and full $\ell^1$ weak-locking errors, uniformly over Eve's measurements. This is an unconditional upper bound for complements of cq-channels.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 5, Proposition 3: accessible-equivocation upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Proposition 3: unconditional accessible-equivocation upper bound.
A normalized fixed Stinespring isometry specifies both channels. -/
theorem schur_locking_upper {A B E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype E] [DecidableEq E] [Nonempty E]
    (V : Matrix (B × E) A ℂ) (hV : Vᴴ * V = 1) (rho : A → Mat E)
    (hCq : CqComplement (environment V) rho) :
    keyedCapacity (dilationMap V) (environment V) true ≤ optimizedEquivocation rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
