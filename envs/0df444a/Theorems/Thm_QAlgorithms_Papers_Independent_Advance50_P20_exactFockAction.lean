-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_exactFockAction
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.exactFockAction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:35:46.031474+00:00
-- url     : https://prove2.me/theorems/b49f359c-9733-4250-bc08-b9f5c62a4e97
-- title:
--   Exact normalized Fock-input output laws for all three families
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Fix an input number state $|j\rangle\langle j|$. With $g_1,g_2,g_3$ the finite binomial factors in Eqs.(13),(17),(21) and $d_\kappa=(1+\kappa^2)^{-1/2}$, the output laws are
--
--   $$\begin{aligned}
--   B(\kappa;n)(|j\rangle\langle j|)&=\sum_{\ell=0}^{j+n}\frac{(j+n-\ell)!\ell!}{j!n!}g_2(n,\ell,j;\kappa)^2|j+n-\ell\rangle\langle j+n-\ell|,\\
--   A(\kappa;n)(|j\rangle\langle j|)&=\kappa^{-2}\sum_{\ell\ge\max(n-j,0)}\frac{j!\ell!}{(j+\ell-n)!n!}g_1(n,j,j+\ell-n;\kappa)^2|j+\ell-n\rangle\langle j+\ell-n|,\\
--   C(\kappa;n)(|j\rangle\langle j|)&=d_\kappa^2\sum_{\ell\ge\max(j-n,0)}\frac{n!\ell!}{(n+\ell-j)!j!}g_3(n,j,n+\ell-j;\kappa)^2|n+\ell-j\rangle\langle n+\ell-j|.
--   \end{aligned}$$
--
--   All weights are nonnegative and sum to one, all series converge in trace norm, and the attenuator output has finite support. The reciprocal-free form of $g_3$ retains $\kappa=0$. These exact input-state identities do not imply the later mixed-input support equalities.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 7, §IV A, unnumbered: exact Fock-state output laws (23),(25),(26)

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

/-- Section IV A, PDF pp.7--8, Eqs.(23),(25),(26): all three exact Fock laws,
with normalized nonnegative weights and trace-norm convergence. For B the sum
is finite (ell<=j+n). Invalid differences are excluded before their use. -/
theorem exactFockAction (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n j : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧ IsDensity (numberDensity j) ∧
    IsDensity (photonChannel c k n (numberDensity j)) ∧
    (∀ ell, 0 ≤ fockWeight c k n j ell) ∧ HasSum (fockWeight c k n j) 1 ∧
    TraceSeries (fun ell => (fockWeight c k n j ell : ℂ) •
      numberDensity (fockOutputIndex c n j ell))
      (photonChannel c k n (numberDensity j)) ∧
    (c = .attenuator →
      photonChannel c k n (numberDensity j) =
        ∑ ell ∈ Finset.range (j + n + 1), (fockWeight c k n j ell : ℂ) •
          numberDensity (j + n - ell)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
