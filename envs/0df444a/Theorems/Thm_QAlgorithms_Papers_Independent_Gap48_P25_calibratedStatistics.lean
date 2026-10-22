-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_calibratedStatistics
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.calibratedStatistics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:45:30.497973+00:00
-- url     : https://prove2.me/theorems/27743562-b2f1-4f04-8624-394bc80ae8f3
-- title:
--   IV.C.1–2: calibrated statistical identities, Eqs.(44)–(48)
-- statement:
--   Let $p_A$ be a normalized photon law, $\widetilde\nu_S>0$, calibrated apparatus transmission $b=t_B\eta\in[0,1]$, $0\le p_d<1/2$, and photon forwarding and line-error probabilities $f_n,\varepsilon_n\in[0,1]$. Assume $f_0=0$, excluding photon creation on vacuum inputs as in footnote 57. In the restricted one-forwarded-photon model define $R_{n,p}=\widetilde\nu_Sp_A(n)f_nb$, $R_{n,d}=\widetilde\nu_Sp_A(n)(1-f_nb)2p_d$ and $R=\sum_n(R_{n,p}+R_{n,d})>0$. For $Y=\sum_nR_{n,p}/R$ and $\delta=(1-Y)/2$,
--
--   $$0\le Y\le1,\qquad Y={1-2p_d\widetilde\nu_S/R\over1-2p_d},\qquad {\sum_nR_{n,d}\over R}=2\delta.$$
--
--   The observed error is $Q=(\sum_nR_{n,p}\varepsilon_n)/R+\delta$, or $Q=Y\varepsilon+\delta$ if $Y>0$ and $\varepsilon$ is the normalized photon-error average. These are calibrated statistical identities, without an unconditional security conclusion.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 31, IV.C.1–2: calibrated statistical identities, Eqs.(44)–(48)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(44)–(48), PDF p.31: calibrated statistical ratio, with IV.C's distinct
Y_n convention and independent dark-count law. Footnote 57 excludes photon
creation on vacuum inputs, so f 0 = 0; no operational security conclusion. -/
theorem calibratedStatistics (p : PhotonLaw) (nu b pd : ℝ) (f e : ℕ → ℝ)
    (hnu : 0 < nu) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hpd : 0 ≤ pd ∧ pd < 1/2)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) (hf0 : f 0 = 0)
    (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1)
    (hR : 0 < calibratedTotal p nu b pd f) :
    let R := calibratedTotal p nu b pd f
    let Y := calibratedFraction p nu b pd f
    let delta := (1-Y)/2
    let photonWrong := ∑' n, calibratedPhoton p nu b f n*e n
    let dark := ∑' n, calibratedDark p nu b pd f n
    Y ∈ Set.Icc (0 : ℝ) 1 ∧ Y = (1-2*pd*nu/R)/(1-2*pd) ∧
    dark/R = 2*delta ∧ (photonWrong+dark/2)/R = (photonWrong/R)+delta ∧
    (0 < Y → (photonWrong+dark/2)/R = Y*(photonWrong/(R*Y))+delta) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
