-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_character_convolution_identity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.character_convolution_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:04:09.991346+00:00
-- url     : https://prove2.me/theorems/582f7b9f-f4c0-4d4c-8436-d8e5989b1a4b
-- title:
--   Lemma 4.9
-- statement:
--   For $\nu\vdash r$, $u\in S_r$, and $d\ge1$,
--
--   $$\mathbb E_{w\sim S_r}[\chi_\nu(w)d^{\ell(uw)}]=\frac{\chi_\nu(u)d^{\uparrow\nu}}{r!}.$$
--
--   The expectation is normalized by $r!$, and $\ell$ counts all cycles including fixed points. This convolution identity is used in the shifted-Schur cancellation formula.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 38, Lemma 4.9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 4.9, arXiv:1501.05028v1, PDF p.38. The character belongs to nu, not the tensor representation. No length≤d premise is required. -/
theorem character_convolution_identity
    (nu : YoungDiagram) (u : Equiv.Perm (Fin nu.card)) (d : ℕ) (hd : 0 < d) :
    ((∑ w : Equiv.Perm (Fin nu.card),
      character nu w * (d : ℝ)^(fullCycle (u*w)).card) / nu.card.factorial) =
      character nu u * contentProduct d nu / nu.card.factorial := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
