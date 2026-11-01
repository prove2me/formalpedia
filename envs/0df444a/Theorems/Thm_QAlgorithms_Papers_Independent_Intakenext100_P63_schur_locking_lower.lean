-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_schur_locking_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.schur_locking_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:18:55.832571+00:00
-- url     : https://prove2.me/theorems/d58efb2b-cedc-43dc-a5f9-aae1bca7ea32
-- title:
--   An unconditional achievable locking rate for complements of cq-channels
-- statement:
--   Let a normalized Stinespring isometry $V:A\to B\otimes E$ on nonzero finite-dimensional spaces define $\mathcal N$ and its complement. Assume $\mathcal N^c(|i\rangle\langle j|)=\delta_{ij}\rho_i$ in the fixed input basis, with normalized $\rho_i$. For any probability vector $p$, set $\bar\rho=\sum_ip_i\rho_i$ and $M_i=\bar\rho^{-1/2}p_i\rho_i\bar\rho^{-1/2}$. Regard these effects as a POVM on $\operatorname{supp}\bar\rho$. Then
--
--   $$L_W(\mathcal N)\ge\widehat H(M)=\min_{\psi\text{ density on }\operatorname{supp}\bar\rho}H(\{\operatorname{Tr}\psi M_i\}_i).$$
--
--   The capacity allows a uniform independent preshared secret of $o(n)$ bits and uniform messages. Decoding error is averaged over messages and key; the full classical $\ell^1$ weak-locking error tends to zero uniformly over all environment POVMs, with a message-independent reference law for each POVM. This is an unconditional rate, with no extractor-success or additivity hypothesis.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 10, Theorem 10: unconditional achievable locking rate for cq complements

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

/-- PDF pp.10–11, Theorem 10: unconditional lower bound with a sublinear secret seed.
No extractor success, additivity conjecture, or invertibility is a hypothesis. -/
theorem schur_locking_lower {A B E : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (V : Matrix (B × E) A ℂ) (hV : Vᴴ * V = 1) (rho : A → Mat E)
    (hCq : CqComplement (environment V) rho) (p : A → ℝ) (hp : IsDistribution p) :
    associatedMinimum p rho ≤ keyedCapacity (dilationMap V) (environment V) true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
