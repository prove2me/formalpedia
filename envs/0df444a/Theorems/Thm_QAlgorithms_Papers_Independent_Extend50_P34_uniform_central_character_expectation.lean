-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_uniform_central_character_expectation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.uniform_central_character_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:52:49.021485+00:00
-- url     : https://prove2.me/theorems/6bd66d62-fdc1-4932-8157-4a37ef21a497
-- title:
--   Corollary 2.35
-- statement:
--   For $d\ge1$, $n\ge0$, and any partition $\mu\vdash k$,
--
--   $$\mathbb E_{\lambda\sim\mathrm{SW}_d^n}p_\mu^\sharp(\lambda)=n^{\downarrow k}d^{\ell(\mu)-k}.$$
--
--   The exponent is signed, and the empty partition gives expectation one. This specializes the central-character moment identity to the uniform spectrum.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 26, Corollary 2.35

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Corollary 2.35, arXiv:1501.05028v1, PDF p.26. Signed integer exponent; d>0; n<|mu| is preserved by the falling factorial. -/
theorem uniform_central_character_expectation
    (d n : ℕ) (hd : 0 < d) (mu : YoungDiagram) :
    expect (n := n) (unif d) (sharp mu) =
      falling n mu.card * (d : ℝ)^((mu.colLen 0 : ℤ) - (mu.card : ℤ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
