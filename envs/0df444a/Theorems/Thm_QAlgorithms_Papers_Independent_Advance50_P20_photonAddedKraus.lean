-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_photonAddedKraus
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.photonAddedKraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:28:49.17989+00:00
-- url     : https://prove2.me/theorems/23e1677c-f91f-4310-887f-ffe5d7083c1d
-- title:
--   The explicit photon-added Kraus families represent the canonical channels
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   For all $\ell,m,j\in\mathbb N$, the entries of the displayed operators are
--
--   $$\begin{aligned}
--   \langle m|A_\ell|j\rangle&=\mathbf1_{m+n=j+\ell}\,\kappa^{-1}\sqrt{\frac{j!\ell!}{m!n!}}\,g_1(n,j,m;\kappa),\\
--   \langle m|B_\ell|j\rangle&=\mathbf1_{m+\ell=j+n}\,\sqrt{\frac{m!\ell!}{j!n!}}\,g_2(n,\ell,j;\kappa),\\
--   \langle m|C_\ell|j\rangle&=\mathbf1_{m+j=n+\ell}\,d_\kappa\sqrt{\frac{n!\ell!}{m!j!}}\,g_3(n,j,m;\kappa),\qquad d_\kappa=(1+\kappa^2)^{-1/2}.
--   \end{aligned}$$
--
--   Here the real finite sums are
--
--   $$\begin{aligned}
--   g_1(n,j,m;\kappa)&=\sum_{r=\max(0,j-m)}^{\min(n,j)}\binom nr\binom m{j-r}(-1)^r\kappa^{-(n+j-2r)}(\sqrt{1-\kappa^{-2}})^{m+2r-j},\\
--   g_2(n,\ell,j;\kappa)&=\sum_{r=\max(0,\ell-n)}^{\min(\ell,j)}\binom jr\binom n{\ell-r}(-1)^{n+r-\ell}\kappa^{j+\ell-2r}(\sqrt{1-\kappa^2})^{2r+n-\ell},\\
--   g_3(n,j,m;\kappa)&=\sum_{r=\max(0,n-j)}^{\min(n,m)}\binom mr\binom j{n-r}(\kappa d_\kappa)^{m+n-2r}(-1)^{n-r}d_\kappa^{j+2r-n}.
--   \end{aligned}$$
--
--   The reciprocal-free expression for $g_3$ includes $\kappa=0$. Each array has its stated bounded-operator realization. For each family $F=A,B,C$, these are Kraus operators for the independently specified channel $\Phi$:
--
--   $$\Phi(X)=\sum_{\ell=0}^\infty F_\ell X F_\ell^\dagger,\qquad \sum_{\ell=0}^\infty F_\ell^\dagger F_\ell=I.$$
--
--   The first series converges unconditionally in trace norm for every trace-class $X$; the second converges strongly. The resulting maps are CPTP. This supplies the explicit operator-sum representations used throughout the paper.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 7, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P20

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P20

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne productCoeff traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad HasFockMatrix operatorOfMatrix KrausComplete
    CoherentRealized IsClassical husimiQ)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation unitaryCoeff conjugateKernel partialRight partialLeft dilationReceiver weakComplement
    boundedUnitaryConjugation traceClassTensorPower operationalTraceClassCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (InterleavedPhase ScaledWeylRepresentation physicalCommutationMatrix
    weylTraceCharacteristic LinearBosonic)

-- Accepted extended bit entropy and mean-photon thermal coefficients.

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits thermalKernel)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, PDF p.7, with Eqs.(11)--(22), PDF pp.5--7: the displayed
families represent the independently defined full channels. Realization,
strong normalization, CPTP, and trace-norm convergence are all conclusions. -/
theorem photonAddedKraus (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧
    IsTraceClassChannel (photonChannel c k n) ∧
    KrausComplete (photonKraus c k n) ∧
    IsKrausRepresentation (photonChannel c k n) (photonKraus c k n) ∧
    ∀ X, IsTraceClass X →
      TraceSeries (fun ell => conjugateKernel (photonKrausMatrix c k n ell) X)
        (photonChannel c k n X) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
