-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_quadraticKrausKernels
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.quadraticKrausKernels
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:38:01.148991+00:00
-- url     : https://prove2.me/theorems/ecf6258b-9759-4e74-ab7c-0a980bb63ffe
-- title:
--   Exact corrected quadratic Kraus kernels
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Write $f_\ell(m,j)=\langle m|F_\ell|j\rangle\in\mathbb R$ for the displayed Kraus entries and $W_{\ell\ell'}=F_\ell^\dagger F_{\ell'}$. Every coefficient is the convergent product sum
--
--   $$\langle j|W_{\ell\ell'}|h\rangle=\sum_{m=0}^\infty f_\ell(m,j)f_{\ell'}(m,h).$$
--
--   For the amplifier, the coefficient is zero unless $n\le j+\ell$ and $h+\ell'=j+\ell$. On that support, put $m=j+\ell-n$; the coefficient is
--
--   $$\kappa^{-2}\sqrt{\frac{j!h!\ell!\ell'!}{(m!)^2(n!)^2}}g_1(n,h,m;\kappa)g_1(n,j,m;\kappa).$$
--
--   For the attenuator it is zero unless $\ell\le j+n$ and $h+\ell=j+\ell'$. With $m=j+n-\ell$, it equals
--
--   $$\sqrt{\frac{(m!)^2\ell!\ell'!}{j!h!(n!)^2}}g_2(n,\ell,j;\kappa)g_2(n,\ell',h;\kappa).$$
--
--   For the conjugator it is zero unless $j\le n+\ell$, $h\le n+\ell'$ and $h+\ell=j+\ell'$. With $m=n+\ell-j$, it equals
--
--   $$d_\kappa^2\sqrt{\frac{(n!)^2\ell!\ell'!}{(m!)^2j!h!}}g_3(n,h,m;\kappa)g_3(n,j,m;\kappa).$$
--
--   Here the $g_i$ are the explicit real finite factors of the corresponding Kraus matrices, and $d_\kappa=(1+\kappa^2)^{-1/2}$. These identities retain all three diagonal branches and do not assert independence within a branch or channel extremality.
--
--   **Formalization Note** Printed Eq.(49) has $(\ell-n+j)!^2$ where the preceding product requires $(\ell+n-j)!^2$; printed Eq.(52) omits the factorial on $j+\ell-\ell'$. The displayed identities correct these unambiguous algebraic errors against Eqs.(14),(18),(22) and the unexpanded products. Independent moderation of these corrections remains required.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 18, Appendix VI A, unnumbered: Kraus quadratic kernels (49)–(52)

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

/-- Appendix VI A, PDF pp.18--19, Eqs.(49)--(52), corrected against the
unexpanded products: (49) uses (ell+n-j)! squared; (52) uses (j+ell-ell')!.
Printed/changed/why are recorded in quadraticEntry and the moderation notes.
These are exact kernels of all pairwise products, including off-diagonal
branches, with zero entries outside the valid ranges. No extremality follows. -/
theorem quadraticKrausKernels (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧
    ∀ ell ell2 j h : ℕ,
      HasSum (fun m => krausEntry c k n ell m j * krausEntry c k n ell2 m h)
        (quadraticEntry c k n ell ell2 j h) ∧
      operatorCoeff ((ContinuousLinearMap.adjoint (photonKraus c k n ell)).comp
        (photonKraus c k n ell2)) j h = (quadraticEntry c k n ell ell2 j h : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
