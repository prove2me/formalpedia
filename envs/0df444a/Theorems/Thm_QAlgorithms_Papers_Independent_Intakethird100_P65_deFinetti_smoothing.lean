-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_deFinetti_smoothing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.deFinetti_smoothing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:58:34.360193+00:00
-- url     : https://prove2.me/theorems/01d14b06-9513-41b3-b495-7ea0f166d83e
-- title:
--   Lemma 11 / Eqs.(84)–(86): permutation-covariant de Finetti smoothing
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A'\to B$ be CPTP, $n\ge1$, and $0<\varepsilon<1$, with $A$ a copy of $A'$. Let $\omega_{(AA')^n}=\int\sigma_{AA'}^{\otimes n}\,d\sigma$ be the Haar pure-state moment, constructed as the normalized symmetric projector, and let $\Omega_{RA^nA'^n}$ be its canonical purification. Set $\tau=(\mathrm{id}_{RA^n}\otimes\mathcal N^{\otimes n})(\Omega)$. Let $K_1$ consist of density matrices $\sigma_{RA^nB^n}$ with $P(\sigma,\tau)\le\varepsilon$ and $\sigma_{RA^n}=\Omega_{RA^n}$. Let $K_2$ consist of outputs $(\mathrm{id}_{RA^n}\otimes\widetilde{\mathcal N})(\Omega)$ at distance at most $\varepsilon$ from $\tau$, with $\widetilde{\mathcal N}$ a permutation-covariant CPTP channel. Then
--
--   $$\inf_{\sigma\in K_1}I_{\max}(RA^n:B^n)_\sigma=\inf_{\sigma\in K_2}I_{\max}(RA^n:B^n)_\sigma.$$
--
--   Covariance means $\widetilde{\mathcal N}\circ\pi_{A'^n}=\pi_{B^n}\circ\widetilde{\mathcal N}$. This explicitly repairs the source's same-forward-permutation notation; the source proof requires inverse input conjugation. The round-one moderator independently checked this minimal inverse-permutation repair; fresh read-backs remain necessary after the other round-one edits.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 20, Lemma 11 / Eqs.(84)–(86): permutation-covariant de Finetti smoothing

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Lemma 11, Eqs.(84)--(86), PDF p.20. The full R A^n reference is fixed.
SOURCE NOTATION REPAIR: Perm is interpreted as covariance (inverse input
conjugation), as required by tensor-power invariance in the printed proof;
no arbitrary-superchannel monotonicity is assumed. The independent round-one
moderator checked that this only repairs the inverse in the permutation action. -/
theorem deFinetti_smoothing (N : Superop A B) (hN : IsChannel N)
    (n : ℕ) (hn : 0 < n) (e : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    infoOnSet (deFinettiK1 N n e) = infoOnSet (deFinettiK2 N n e) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
