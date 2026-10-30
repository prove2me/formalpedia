-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_adjacent_kl_quantitative
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.adjacent_kl_quantitative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:14:19.082364+00:00
-- url     : https://prove2.me/theorems/620d27f9-9f8e-49fe-ab79-1e76a0f2ad2d
-- title:
--   Theorem 5.10
-- statement:
--   There is an absolute $b>0$ such that for $n=r^2/\omega^2$ and $200\le\omega\le\sqrt r$,
--
--   $$D_{\rm KL}(\mathrm{SW}_r^n\|\mathrm{SW}_{r+1}^n)\le\exp\!\left(b(\log r/\log\omega)^{2.01}\right)\omega^{-2}.$$
--
--   In particular a suitable absolute $B>0$ and $\omega(r)=\exp(B(\log r)^{0.67})$ give divergence tending to zero at $n=\lfloor r^2/\omega(r)^2\rfloor$. Copy discarding handles the integer floor. This yields the nearly quadratic rank-distinguishing lower bound.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 52, Theorem 5.10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 5.10, arXiv:1501.05028v1, PDF p.52. Source p.52 visually has omega≤sqrt(r), despite extraction losing the radical. The in-particular O specifies a suitable choice, not every upper-O-bounded omega. -/
theorem adjacent_kl_quantitative
    : (∃ b : ℝ, 0 < b ∧ ∀ r n : ℕ, ∀ omega : ℝ,
        RankRegime r n omega → adjacentKL r n ≤
          Real.exp (b*Real.rpow (Real.log r/Real.log omega) (201/100 : ℝ))/omega^2) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ delta : ℝ, 0 < delta → ∃ r0 : ℕ,
        ∀ r : ℕ, r0 ≤ r →
          adjacentKL r ⌊(r : ℝ)^2/(chosenOmega B r)^2⌋₊ ≤ delta) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
