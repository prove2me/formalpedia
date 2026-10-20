-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_four_bell_candidate_npt
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.four_bell_candidate_npt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:29:31.713035+00:00
-- url     : https://prove2.me/theorems/0b04e651-8af5-4e5a-ac60-1b8fb399508f
-- title:
--   §XII: the four-Bell hiding candidate is NPT
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $d\ge2$, $k\ge1$, and let $\tau_1=((\rho_s+\rho_a)/2)^{\otimes k}$, $\tau_2=\rho_s^{\otimes k}$ be the hiding states. Write $|\phi^\pm\rangle=(|00\rangle\pm|11\rangle)/\sqrt2$ and $|\psi^\pm\rangle=(|01\rangle\pm|10\rangle)/\sqrt2$. The operator
--
--   $$\rho=\tfrac14\bigl(P_{\phi^+}\otimes\tau_1\otimes\tau_1+P_{\phi^-}\otimes\tau_1\otimes\tau_2+P_{\psi^+}\otimes\tau_2\otimes\tau_1+P_{\psi^-}\otimes\tau_2\otimes\tau_2\bigr)$$
--
--   is a normalized state and has negative partial transpose across the full Alice:Bob cut, including both hiding flags. Here $P_v=|v\rangle\langle v|$. This is an NPT candidate; its bound entanglement is not asserted.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 28, §XII: the four-Bell hiding candidate is NPT

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.28–30, Eqs.(178)–(185): normalized four-Bell candidate is NPT.
The 1/4 in block display (180) must be 1/8, as fixed by (178). No bound-entanglement claim. -/
theorem four_bell_candidate_npt (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    IsDensityMatrix (nptCandidate d k) ∧ ¬ (transposeBob (nptCandidate d k)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
