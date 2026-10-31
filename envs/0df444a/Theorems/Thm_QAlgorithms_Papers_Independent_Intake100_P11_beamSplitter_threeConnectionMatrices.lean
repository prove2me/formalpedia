-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_beamSplitter_threeConnectionMatrices
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.beamSplitter_threeConnectionMatrices
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:55:53.020678+00:00
-- url     : https://prove2.me/theorems/e4127b6c-9b51-479d-882c-f05c7118ff39
-- title:
--   Supporting beam-splitter cube identity and source-module ancilla count
-- statement:
--   For intensity reflectivity $R\in[0,1]$, define
--
--   $$
--   B_R=\begin{pmatrix}\sqrt R&\sqrt{1-R}\\\sqrt{1-R}&-\sqrt R\end{pmatrix},\quad
--   k_1=\sqrt R-\sqrt{1-R},\quad k_2=-\sqrt R-\sqrt{1-R},\quad \eta=-\sqrt{1-R}.
--   $$
--
--   Let $C(k_1,k_2,\eta)$ be the connection matrix of Eq.(16), in grouped coordinates. Then
--
--   $$
--   B_R^2=I_2,\qquad C(k_1,k_2,\eta)^3=\operatorname{diag}(B_R,B_R).
--   $$
--
--   The chronological program with three identical source modules has this matrix and uses $3\times3=9$ ancillas. Both endpoints are included: $R=0$ swaps the modes, and $R=1$ gives opposite signs on the two modes.
--
--   This is supporting ideal algebra and construction bookkeeping. The full assertion that the operational composed module acts as the beam-splitter channel on every normal input remains deferred.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 9, §VI, Eqs.(17)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF p.9, Eqs.(17)--(19): SUPPORTING cube identity and nine-ancilla count
for three source modules, including both intensity-reflectivity endpoints.
The all-normal-state operational node is deferred; a matrix is not a channel. -/
theorem beamSplitter_threeConnectionMatrices
    (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    let settings := beamSettings R
    let program := List.replicate 3 settings
    phaseFreeBeamMatrix R * phaseFreeBeamMatrix R = 1 ∧
    connectionMatrix settings.kappa1 settings.kappa2 settings.eta ^ 3 =
      beamSplitterGrouped R ∧
    connectionWord program = beamSplitterGrouped R ∧
    connectionAncillas program = 9 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
