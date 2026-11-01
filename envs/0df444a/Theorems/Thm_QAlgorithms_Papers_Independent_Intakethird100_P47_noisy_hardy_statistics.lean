-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_noisy_hardy_statistics
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.noisy_hardy_statistics
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:35:23.985952+00:00
-- url     : https://prove2.me/theorems/ec476dd9-91ab-4312-af0b-bd7a0767790c
-- title:
--   White-noise Hardy statistics with signed functionals
-- statement:
--   For each party $P\in\{A,B\}$, let $\alpha_P,\beta_P\in\mathbb C$ satisfy $|\alpha_P|^2+|\beta_P|^2=1$ and $0<|\alpha_P|<1$. The unprimed measurement basis is $|0\rangle,|1\rangle$, and the primed basis is $|0'\rangle_P=\alpha_P|0\rangle+\beta_P|1\rangle$, $|1'\rangle_P=\overline{\beta_P}|0\rangle-\overline{\alpha_P}|1\rangle$. Write $|\psi_H\rangle$ for the last vector obtained by the ordered Gram–Schmidt construction (2)–(4), and $p_H(a,b\mid A,B)$ for its Born probabilities.
--
--   Let $0\le\eta\le1$, let $q=p_H(00\mid00)$, and measure the state $\rho(\eta)=(1-\eta)I_4/4+\eta|\psi_H\rangle\langle\psi_H|$ in these bases. This is a density matrix, with
--   $$
--   p_\eta(00\mid00)=\eta q+\frac{1-\eta}{4},\qquad
--   p_\eta(00\mid10)=p_\eta(00\mid01)=p_\eta(11\mid11)=\frac{1-\eta}{4}.
--   $$
--   For $H=(p(00\mid00),-p(00\mid10),-p(00\mid01),-p(11\mid11))$, as defined by the coefficients after (12),
--   $$
--   H(p_\eta)=\left(\eta q+\frac{1-\eta}{4},-\frac{1-\eta}{4},-\frac{1-\eta}{4},-\frac{1-\eta}{4}\right).
--   $$
--   This keeps event probabilities and signed functionals distinct, with $\eta=1$ the ideal state.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 6, IV B–C: noisy statistics (13), (16), with signed H convention

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- IV B–C, PDF pp.5–6, (13),(16): event probabilities and signed H values.
Printed (16) has positive h2,h3,h4; changed to negative values, forced by the negative
coefficients defining H in (12), p.5. eta remains visibility, with eta=1 ideal.
This source correction requires independent moderation. -/
theorem noisy_hardy_statistics (d : HardyParameters) (eta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) :
    let p := hardyBehavior d (noisyHardy d eta)
    let q := hardyBehavior d (pureDensity (psiH d)) false false false false
    IsDensityMatrix (noisyHardy d eta) ∧
    p false false false false = eta * q + (1 - eta) / 4 ∧
    p true false false false = (1 - eta) / 4 ∧
    p false true false false = (1 - eta) / 4 ∧
    p true true true true = (1 - eta) / 4 ∧
    hardyStatistics p = ![eta * q + (1 - eta) / 4,
      -(1 - eta) / 4, -(1 - eta) / 4, -(1 - eta) / 4] := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
