-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_coherence_bell_overlap
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.coherence_bell_overlap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:15:47.323896+00:00
-- url     : https://prove2.me/theorems/d3384ffd-82da-4b0f-953a-eb403c7f2e3e
-- title:
--   Lemma 4: coherence and Bell overlap, corrected boundary
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   For a two-qubit density $\rho$, let $c=\operatorname{Re}\langle00|\rho|11\rangle$, $P^+=|\psi^+\rangle\langle\psi^+|$, and $|\psi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$. For $\epsilon\ge0$,
--
--   $$\operatorname{Tr}(\rho P^+)>1-\epsilon\ \Longrightarrow\ c>\tfrac12-\epsilon,$$
--   $$c>\tfrac12-\epsilon\ \Longrightarrow\ \operatorname{Tr}(\rho P^+)\ge1-2\epsilon.$$
--
--   These implications relate Bell overlap to key coherence. The first antecedent follows the strict version in Appendix XV-G.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 12, Lemma 4: coherence and Bell overlap, corrected boundary

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

/-- PDF pp.12–13, Lemma 4; p.39, Eq.(280): printed (61)'s >= then > fails at
boundary equality. Use the STRICT first antecedent of the source's Appendix XV-G. -/
theorem coherence_bell_overlap (rho : Op (Key 2)) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (((rho * bellProjector 2).trace.re > 1-eps) → (rho (0,0) (1,1)).re > 1/2-eps) ∧
    ((rho (0,0) (1,1)).re > 1/2-eps → (rho * bellProjector 2).trace.re ≥ 1-2*eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
