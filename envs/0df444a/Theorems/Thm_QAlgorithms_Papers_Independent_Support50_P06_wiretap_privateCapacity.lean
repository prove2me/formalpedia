-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_wiretap_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P06.wiretap_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:28:14.354716+00:00
-- url     : https://prove2.me/theorems/88ddd64e-805d-43ee-95ed-765f3c353d2c
-- title:
--   Conditional bosonic private capacity, additivity and Gaussian coherent achievability
-- statement:
--   Consider the full single-mode noiseless bosonic wiretap channel with vacuum environment, Bob transmissivity $0\le\eta\le1$, and complementary Eve output from the same lossless beam splitter. Let $\bar N\ge0$ be a finite photon budget. Use unassisted classical private codes with arbitrary normalized mixed, possibly entangled block inputs, uniform messages, independent private discrete encoder randomness, and a normalized POVM decoder. The unconditional total input photon number, averaged over messages and randomness, is at most $n\bar N$ in an $n$-use block. For every message and random branch, decoding success exceeds $1-\epsilon$; Holevo leakage about the message, after averaging the private randomness, tends to zero. Rates are $\ln M/n$ nats/use.
--
--   Assume global minimum output entropy conjecture 2: for every positive number of modes and every entropy shell $S(\rho)=ng(K)$, mixing $\rho$ with vacuum has minimum output entropy $ng((1-\eta)K)$, attained by identical thermal inputs. Then
--
--   $$C_p(\eta,\bar N)=\begin{cases}g(\eta\bar N)-g((1-\eta)\bar N),&\eta>1/2,\0,&\eta\le1/2,\end{cases}\qquad g(x)=(x+1)\ln(x+1)-x\ln x.$$
--
--   This rate is asymptotically achievable with product coherent signal states and collective block decoding, and restricting the encoder to such states leaves the capacity unchanged. For every positive $n$, the unrestricted $n$-letter private-information supremum under total budget $n\bar N$ equals $nC_p(\eta,\bar N)$; grouping any positive number of parallel identical modes multiplies operational capacity by that number. On the $\eta>1/2$ branch, the single-use coherent ensemble with isotropic prior $p(\alpha)=e^{-|\alpha|^2/\bar N}/(\pi\bar N)$ has private information $g(\eta\bar N)-g((1-\eta)\bar N)$ and thermal average input of mean $\bar N$. Individual coherent signals have pure outputs at both receivers. At $\bar N=0$ the prior is the point mass at vacuum.
--
--   This identifies the conditional operational capacity and its single-use signal ensemble, while allowing arbitrarily long codes.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 3, §III, unnumbered Theorem, (10): conditional bosonic wiretap privacy capacity, additivity and coherent-state achievability

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

/-- PDF pp.2–3, §III Theorem, (10): conditional operational privacy capacity,
additivity, and coherent-state achievability with the printed Gaussian prior.
Printed (5) uses j=(m,k); changed to Holevo secrecy of m after averaging k,
because (6) and the proof use secret MESSAGE information. Rates use ln(M)/n
instead of the printed bit-count notation 2^(nR). At Nbar=0 the Gaussian prior
is its vacuum point mass. The Gaussian assertion concerns eta>1/2; zero rate
is achievable below that threshold. No one-shot error-free claim is made. -/
theorem wiretap_privateCapacity (hmoe : StrongConjecture2)
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
