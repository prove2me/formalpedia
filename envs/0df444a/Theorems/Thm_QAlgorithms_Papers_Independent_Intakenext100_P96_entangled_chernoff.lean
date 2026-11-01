-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_entangled_chernoff
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.entangled_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:50:14.847757+00:00
-- url     : https://prove2.me/theorems/53fbd203-fff0-4dda-aa51-bafab891fe48
-- title:
--   Exact retained-model entangled Chernoff factor
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
--   For every $0<s<1$ the overlap equals
--   $$
--   \operatorname{Tr}(\sigma_0^{1-s}\sigma_1^s)
--   =F_d(b,\eta,s)
--   =(1-\eta)^s\!\left[1+\frac bd
--     \left(-1+\left(1+\frac{\eta d}{(1-\eta)b}\right)^s\right)\right].
--   $$
--   Consequently,
--   $$
--   Q(\sigma_0,\sigma_1)=\inf_{0<s<1}F_d(b,\eta,s)
--   =\min_{0\le s\le1}F_d(b,\eta,s),
--   $$
--   and the minimum is attained by some $s\in[0,1]$. This is the exact first line of (11) for the retained model; it does not assert the second line's remainder.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 7, Exact retained-model entangled Chernoff factor, first line of (11) on p.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, first equality of (11): exact retained-model overlap and Chernoff
factor. b>0 and eta<1 exclude the printed denominator's singularities.
The second equality's asymptotic remainder is separately deferred. -/
theorem entangled_chernoff (p : ModelParameters) (hb : 0 < p.b)
    (hdb : (p.d : ℝ) * p.b < 1) (heta0 : 0 < p.eta) (heta1 : p.eta < 1) :
    (∀ s ∈ Set.Ioo (0 : ℝ) 1,
      QAlgorithms.Papers.Independent.Claimed50.P15.petzOverlap
        (pairPresent p.d p.b p.eta) (pairAbsent p.d p.b) s =
        entangledFactor p.d p.b p.eta s) ∧
    illuminationChernoffFactor (pairAbsent p.d p.b) (pairPresent p.d p.b p.eta) =
      sInf ((fun s : ℝ => entangledFactor p.d p.b p.eta s) '' Set.Ioo 0 1) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) 1,
      illuminationChernoffFactor (pairAbsent p.d p.b) (pairPresent p.d p.b p.eta) =
        entangledFactor p.d p.b p.eta s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
