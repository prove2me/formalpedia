-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_central_character_moment_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.central_character_moment_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:11:11.672921+00:00
-- url     : https://prove2.me/theorems/71e5758a-1e19-4ac7-a881-7f2d30babbe4
-- title:
--   Lemma 5.6
-- statement:
--   Let $r,n\ge1$, $200\le\omega\le\sqrt r$, and $n=r^2/\omega^2$. For every partition $\mu$,
--
--   $$0\le\mathbb E_{\lambda\sim\mathrm{SW}_r^n}p_\mu^\sharp(\lambda)\le r^{\mathrm{wt}(\mu)}(1/\omega^2)^{|\mu|}.$$
--
--   The empty partition gives equality $1\le1$. This bounds the expectations of lower-weight observables.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 50, Lemma 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.6, arXiv:1501.05028v1, PDF p.50. Empty mu included; positive bases make all powers meaningful. Standing regime retained. -/
theorem central_character_moment_bound
    (r n : ℕ) (omega : ℝ) (hregime : RankRegime r n omega) (mu : YoungDiagram) :
    0 ≤ expect (n := n) (unif r) (sharp mu) ∧
      expect (n := n) (unif r) (sharp mu) ≤ (r : ℝ)^observableWeight mu * (1/omega^2)^mu.card := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
