-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_ns_exact_fidelity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.ns_exact_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:59:28.474408+00:00
-- url     : https://prove2.me/theorems/39267213-88c2-466e-88eb-f00e7a0138ae
-- title:
--   Exact NS coding fidelity and agreement of conventions
-- statement:
--   Let $E$ be a finite-dimensional CPTP channel and $d\ge1$ an integer. Let $\mathbb S_{\rm NS}$ be the maximal deterministic physical replacement-channel-preserving code family. For squared worst-case channel fidelity $F$ and fixed normalized maximally entangled-input fidelity $\widetilde F$,
--   $$
--   \max_{\Theta\in\mathbb S_{\rm NS}}F(\Theta(E),\operatorname{id}_d)
--   =G_{\mathcal O_R}(E;d^2)
--   =\max_{\Theta\in\mathbb S_{\rm NS}}\widetilde F(\Theta(E),\operatorname{id}_d).
--   $$
--   The ordinary gauge uses reference-assisted effects whose overlap with every replacement channel is at most $1/d^2$. Both channel optimizations have physical maximizing codes.
--
--   This concrete equality restores the suppressed target parameter on p.13; it does not assert the unrestricted fixed-input extension of the general theorems.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 13, Exact NS coding fidelity and agreement of conventions

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Concrete NS fidelity application, PDF pp.4,13. The target parameter
suppressed in the quoted sentence is d^2. Both fidelity optimizations attain
the same value; this does not assert the unrestricted ambiguous Remark (D10). -/
theorem ns_exact_fidelity {p : Port} (E : ChannelChoi p) (hE : CPTP E) (d : ℕ+) :
    let O := communicationTheory .ns
    bestFidelity O E (identityChoi d) = gauge O E (((d : ℝ≥0∞) ^ 2)⁻¹) ∧
    bestChoiFidelity O E (identityChoi d) = bestFidelity O E (identityChoi d) ∧
    (∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi (transmissionPort d), FreeSuperchannel O Theta ∧
      ENNReal.ofReal (worstCaseFidelity (Theta E) (identityChoi d)) = bestFidelity O E (identityChoi d)) ∧
    (∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi (transmissionPort d), FreeSuperchannel O Theta ∧
      ENNReal.ofReal (choiFidelity (Theta E) (identityChoi d)) = bestChoiFidelity O E (identityChoi d)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
