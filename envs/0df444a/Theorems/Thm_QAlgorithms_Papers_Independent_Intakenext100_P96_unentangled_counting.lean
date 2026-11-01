-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_unentangled_counting
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.unentangled_counting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:48:58.055089+00:00
-- url     : https://prove2.me/theorems/fca9fa16-752c-41a4-8ddd-31b2abf0fc8d
-- title:
--   Unentangled counting attains the collective Chernoff rate
-- statement:
--   Work in the retained vacuum/single-photon model, on a signal space with vacuum $|\mathrm{vac}\rangle$ and $d\ge1$ orthogonal single-photon modes. Let $b\ge0$ be the background probability per mode, with $db\le1$, and let $0\le\eta\le1$ be the reflection probability. Set
--   $$
--   \rho_0=(1-db)|\mathrm{vac}\rangle\langle\mathrm{vac}|+b\sum_{k=1}^d|k\rangle\langle k|.
--   $$
--
--   Let $|\psi\rangle$ be any unit single-photon vector with zero vacuum amplitude, let $P_\psi=|\psi\rangle\langle\psi|$, and put $\rho_1=(1-\eta)\rho_0+\eta P_\psi$.
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
--   For $p_0=b$ and $p_1=b(1-\eta)+\eta$,
--   $$
--   \lim_{n\to\infty}(2E_n^*)^{1/n}
--   =\lim_{n\to\infty}\bigl(2C_n(p_0,p_1)\bigr)^{1/n}
--   =Q(\rho_0,\rho_1)=B(p_0,p_1).
--   $$
--   Thus the projector measurement repeated on each copy, followed by optimal count-based decisions, attains the collective error exponent. The factor depends only on $b,\eta$, independently of $d$ and the unit input $|\psi\rangle$.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 5, Unentangled photon counting is asymptotically optimal and independent of d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--5: counting signal-projector outcomes with optimal classical
postprocessing attains the quantum Chernoff rate, independently of d and psi.
No finite-n equality of collective and counting errors is asserted. -/
theorem unentangled_counting (p : ModelParameters) (hb : 0 < p.b)
    (hdb : (p.d : ℝ) * p.b < 1) (heta0 : 0 < p.eta) (heta1 : p.eta < 1)
    (psi : EuclideanSpace ℂ (Fin p.d)) (hpsi : IsState psi) :
    illuminationChernoffFactor (background p.d p.b) (signalPresent p.b p.eta psi) =
      binaryChernoff p.b (p.b * (1 - p.eta) + p.eta) ∧
    Tendsto (errorFactor (iidEqualPriorError (background p.d p.b) (signalPresent p.b p.eta psi)))
      atTop (nhds (binaryChernoff p.b (p.b * (1 - p.eta) + p.eta))) ∧
    Tendsto (errorFactor (countingError p.b (p.b * (1 - p.eta) + p.eta)))
      atTop (nhds (binaryChernoff p.b (p.b * (1 - p.eta) + p.eta))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
