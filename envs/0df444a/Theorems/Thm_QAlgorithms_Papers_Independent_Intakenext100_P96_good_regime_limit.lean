-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_good_regime_limit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.good_regime_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:50:54.508456+00:00
-- url     : https://prove2.me/theorems/43c39743-36e8-463f-ba66-e8d21f99e5a3
-- title:
--   Common high-SNR limit and the factor-d good-regime threshold shift
-- statement:
--   Fix an integer $d\ge1$, a reflection probability $0<\eta<1$, and a unit single-photon input $|\psi\rangle$. For each sufficiently small positive $b$, let $\rho_0,\rho_1,\sigma_0,\sigma_1$ be the retained unentangled and entangled pairs described by (1.0),(1.1),(8.0),(8.1), using the perfectly retained resource $|\Phi_d\rangle=d^{-1/2}\sum_k|k\rangle_S|k\rangle_A$. In particular, $\rho_1=(1-\eta)\rho_0+\eta|\psi\rangle\langle\psi|$, $\sigma_0=\rho_0\otimes I_A/d$ and $\sigma_1=(1-\eta)\sigma_0+\eta|\Phi_d\rangle\langle\Phi_d|$.
--
--   For states $a_0,a_1$, write $Q(a_0,a_1)=\inf_{0<s<1}\operatorname{Tr}(a_0^{1-s}a_1^s)$, including one-sided limits at singular endpoints.
--   Then
--   $$
--   \lim_{b\downarrow0}Q(\rho_0,\rho_1)
--   =\lim_{b\downarrow0}Q(\sigma_0,\sigma_1)=1-\eta.
--   $$
--   The source's good-regime inequalities are, for every $b>0$,
--   $$
--   \eta/b>1\iff b<\eta,\qquad
--   \eta d/b>1\iff b<d\eta.
--   $$
--   Thus the good regime has a noise threshold larger by a factor $d$. This specifies a fixed-$d$, fixed-$\eta$ leading limit, with $db<1$ eventually, rather than a finite-ratio approximation or a claimed remainder.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 8, Good-regime leading Chernoff limit; repeated label (11) on p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4,8, repeated label (11) on p.8: with d, eta and the input fixed,
the high-SNR limit b tending to zero gives 1-eta for both factors. The good
regime's noise threshold is multiplied by d. Printed "d/b>1" for the
unentangled case on p.8 is corrected to "eta/b>1", consistently with p.3.
This states no O((db)^2) remainder. -/
theorem good_regime_limit (d : ℕ) (hd : 0 < d) (eta : ℝ)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (psi : EuclideanSpace ℂ (Fin d)) (hpsi : IsState psi) :
    Tendsto (fun b : ℝ => illuminationChernoffFactor (background d b) (signalPresent b eta psi))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - eta)) ∧
    Tendsto (fun b : ℝ => illuminationChernoffFactor (pairAbsent d b) (pairPresent d b eta))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - eta)) ∧
    (∀ b : ℝ, 0 < b →
      (1 < eta / b ↔ b < eta) ∧
      (1 < eta * (d : ℝ) / b ↔ b < (d : ℝ) * eta)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
