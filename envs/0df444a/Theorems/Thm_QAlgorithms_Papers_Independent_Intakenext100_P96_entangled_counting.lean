-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_entangled_counting
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.entangled_counting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:51:35.638628+00:00
-- url     : https://prove2.me/theorems/f95c4c2c-0958-4dda-a226-98012d573723
-- title:
--   Repeated joint tests attain the collective Chernoff rate
-- statement:
--   Work in the retained vacuum/single-photon model, on a signal space with vacuum $|\mathrm{vac}\rangle$ and $d\ge1$ orthogonal single-photon modes. Let $b\ge0$ be the background probability per mode, with $db\le1$, and let $0\le\eta\le1$ be the reflection probability. Set
--   $$
--   \rho_0=(1-db)|\mathrm{vac}\rangle\langle\mathrm{vac}|+b\sum_{k=1}^d|k\rangle\langle k|.
--   $$
--
--   Use the resource $|\Phi_d\rangle=d^{-1/2}\sum_{k=1}^d|k\rangle_S|k\rangle_A$, transmitting only the signal and retaining the ancillary photon perfectly. Write $P_\Phi=|\Phi_d\rangle\langle\Phi_d|$, $\sigma_0=\rho_0\otimes I_A/d$, and $\sigma_1=(1-\eta)\sigma_0+\eta P_\Phi$.
--
--   For this statement assume $0<b$, $db<1$, and $0<\eta<1$.
--
--   For states $a_0,a_1$, write $Q(a_0,a_1)=\inf_{0<s<1}\operatorname{Tr}(a_0^{1-s}a_1^s)$, including one-sided limits at singular endpoints.
--
--   Prepare identical inputs independently with independent background noise, keeping all parameters fixed across trials. Let $E_n^*$ be the minimum equal-prior error among all joint binary effects on the $n$ returned copies. Let
--   $$
--   C_n(p_0,p_1)=\frac12\sum_{k=0}^{n}\min\!\left\{\binom nk p_0^k(1-p_0)^{n-k},\binom nk p_1^k(1-p_1)^{n-k}\right\}
--   $$
--   be the minimum error after recording the full number of yes outcomes, for yes probabilities $p_0,p_1$ under the two hypotheses. Define
--   $$
--   B(p_0,p_1)=\inf_{0<s<1}\left[(1-p_0)^{1-s}(1-p_1)^s+p_0^{1-s}p_1^s\right].
--   $$
--
--   Repeat the ideal joint measurement $\{P_\Phi,I-P_\Phi\}$ on each returning signal and its own retained ancilla. With $p_0=b/d$ and $p_1=(1-\eta)b/d+\eta$,
--   $$
--   \lim_{n\to\infty}(2E_n^*)^{1/n}
--   =\lim_{n\to\infty}\bigl(2C_n(p_0,p_1)\bigr)^{1/n}
--   =Q(\sigma_0,\sigma_1)=B(p_0,p_1).
--   $$
--   This states that these separate measurements followed by optimal decisions from the full count attain the unrestricted collective error exponent. It does not identify single-shot error with many-copy error or assert an efficient physical detector.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 8, Repeated joint yes/no measurements attain the entangled Chernoff rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7--8: repeated joint yes/no tests with optimal count postprocessing
attain the collective Chernoff rate. This is not equality of single-shot and
many-copy error probabilities, nor a claim of efficient detector implementation. -/
theorem entangled_counting (p : ModelParameters) (hb : 0 < p.b)
    (hdb : (p.d : ℝ) * p.b < 1) (heta0 : 0 < p.eta) (heta1 : p.eta < 1) :
    illuminationChernoffFactor (pairAbsent p.d p.b) (pairPresent p.d p.b p.eta) =
      binaryChernoff (p.b / (p.d : ℝ)) ((1 - p.eta) * (p.b / (p.d : ℝ)) + p.eta) ∧
    Tendsto (errorFactor (iidEqualPriorError (pairAbsent p.d p.b) (pairPresent p.d p.b p.eta)))
      atTop (nhds (binaryChernoff (p.b / (p.d : ℝ))
        ((1 - p.eta) * (p.b / (p.d : ℝ)) + p.eta))) ∧
    Tendsto (errorFactor (countingError (p.b / (p.d : ℝ))
        ((1 - p.eta) * (p.b / (p.d : ℝ)) + p.eta)))
      atTop (nhds (binaryChernoff (p.b / (p.d : ℝ))
        ((1 - p.eta) * (p.b / (p.d : ℝ)) + p.eta))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
