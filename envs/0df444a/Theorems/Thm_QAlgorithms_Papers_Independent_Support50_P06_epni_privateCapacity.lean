-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_epni_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P06.epni_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:37:36.138525+00:00
-- url     : https://prove2.me/theorems/4900bfb5-7062-45fd-9de9-e46187d87d47
-- title:
--   EPnI implies the full bosonic private-capacity conclusion
-- statement:
--   Consider the full single-mode noiseless bosonic wiretap channel with vacuum environment, Bob transmissivity $0\le\eta\le1$, and complementary Eve output from the same lossless beam splitter. Let $\bar N\ge0$ be a finite photon budget. Use unassisted classical private codes with arbitrary normalized mixed, possibly entangled block inputs, uniform messages, independent private discrete encoder randomness, and a normalized POVM decoder. The unconditional total input photon number, averaged over messages and randomness, is at most $n\bar N$ in an $n$-use block. For every message and random branch, decoding success exceeds $1-\epsilon$; Holevo leakage about the message, after averaging the private randomness, tends to zero. Rates are $\ln M/n$ nats/use.
--
--   Assume global EPnI for all positive mode counts and transmissivities in $[0,1]$, with independent normalized port states of finite input entropies; output entropy may be infinite. Then
--
--   $$C_p(\eta,\bar N)=\begin{cases}g(\eta\bar N)-g((1-\eta)\bar N),&\eta>1/2,\0,&\eta\le1/2,\end{cases}\qquad g(x)=(x+1)\ln(x+1)-x\ln x.$$
--
--   This rate is asymptotically achievable with product coherent signal states and collective block decoding, and restricting the encoder to such states leaves the capacity unchanged. For every positive $n$, the unrestricted $n$-letter private-information supremum under total budget $n\bar N$ equals $nC_p(\eta,\bar N)$; grouping any positive number of parallel identical modes multiplies operational capacity by that number. On the $\eta>1/2$ branch, the single-use coherent ensemble with isotropic prior $p(\alpha)=e^{-|\alpha|^2/\bar N}/(\pi\bar N)$ has private information $g(\eta\bar N)-g((1-\eta)\bar N)$ and thermal average input of mean $\bar N$. Individual coherent signals have pure outputs at both receivers. At $\bar N=0$ the prior is the point mass at vacuum.
--
--   This identifies the conditional operational capacity and its single-use signal ensemble, while allowing arbitrarily long codes.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 5, Abstract and §VI: EPnI implies the wiretap-capacity theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1 abstract and p.5 §VI: EPnI implies the entire conditional privacy
capacity conclusion, including additivity and Gaussian coherent achievability.
Source correction: (5) prints j=(m,k); secrecy here concerns m after averaging
k, as required by (6) and the proof. Nats use ln(M)/n; Nbar=0 uses delta_0.
This theorem does not assert the EPnI conjecture or an operational quantum code. -/
theorem epni_privateCapacity (hepni : EntropyPhotonNumberInequality)
    (eta Nbar : ℝ) (heta : 0 ≤ eta) (heta_one : eta ≤ 1) (hNbar : 0 ≤ Nbar) :
    holevoMessagePrivacyCapacityNats 1 eta Nbar =
      ENNReal.ofReal (if 1 / 2 < eta then g (eta * Nbar) - g ((1 - eta) * Nbar) else 0) ∧
    holevoMessagePrivacyCapacityNats 1 eta Nbar true = holevoMessagePrivacyCapacityNats 1 eta Nbar ∧
    privateAchievable 1 eta Nbar true
      (if 1 / 2 < eta then g (eta * Nbar) - g ((1 - eta) * Nbar) else 0) ∧
    (∀ n : ℕ, 0 < n → blockPrivateInformation n eta Nbar =
      (((n : ℝ) * (if 1 / 2 < eta then
        g (eta * Nbar) - g ((1 - eta) * Nbar) else 0) : ℝ) : EReal)) ∧
    (∀ width : ℕ, 0 < width → holevoMessagePrivacyCapacityNats width eta Nbar =
      (width : ℝ≥0∞) * holevoMessagePrivacyCapacityNats 1 eta Nbar) ∧
    (1 / 2 < eta →
      gaussianPrivateInformation eta Nbar = g (eta * Nbar) - g ((1 - eta) * Nbar) ∧
      coherentMixture Nbar = identicalThermalKernel 1 Nbar ∧
      ∀ alpha : ℂ,
        spectralEntropyNats (pureLoss 1 eta (productCoherentKernel 1 (fun _ => alpha))) = 0 ∧
        spectralEntropyNats ((charlieMarginal (broadcast 1 eta (productCoherentKernel 1 (fun _ => alpha))))) = 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
