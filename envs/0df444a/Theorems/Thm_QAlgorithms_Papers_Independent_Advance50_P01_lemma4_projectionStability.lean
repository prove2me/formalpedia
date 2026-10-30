-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_lemma4_projectionStability
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.lemma4_projectionStability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:02:33.342082+00:00
-- url     : https://prove2.me/theorems/76046415-0ef8-4f15-9477-e7c02c5236cb
-- title:
--   Lemma 4: stability under an orthogonal projection
-- statement:
--   Let $\phi,\varphi$ be unit vectors in a complex Hilbert space, let $\pi$ be a bounded orthogonal projection (self-adjoint and idempotent), and let $\varepsilon\in\mathbb R$ satisfy $\|\phi-\pi\phi\|\le\varepsilon$. With the Hilbert norm and the rank-one operator $R_\phi v=\langle\phi|v\rangle\phi$, we have
--
--   $$\|R_\phi\varphi\|^2-\|\pi R_\phi\pi\varphi\|^2\le2\sqrt2\,\varepsilon.$$
--
--   This bounds the signed loss under projection in arbitrary dimension. The norm hypothesis already forces nonnegative tolerance.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 8, Lemma 4, equation (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P01

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Advance50.P01

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile tensorPower)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

attribute [local instance] Classical.propDecidable

-- Match the universe-zero matrix indices of the pinned accepted interfaces.

variable {I : Type} [Fintype I] [DecidableEq I]

-- SupportIncluded is opened directly from the accepted Information100.P71 module.

/-- Lemma 4, source PDF p. 8, (16), appendix p. 18. The projector is self-adjoint and
idempotent on an arbitrary complex Hilbert space. The difference is signed and the constant
is exactly 2 sqrt(2). Nonnegativity of epsilon follows from the norm hypothesis. -/
theorem lemma4_projectionStability {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (phi varphi : E)
    (hphi : ‖phi‖ = 1) (hvarphi : ‖varphi‖ = 1) (pi : E →L[ℂ] E)
    (hself : ∀ x y, inner ℂ (pi x) y = inner ℂ x (pi y))
    (hidempotent : ∀ x, pi (pi x) = pi x) (epsilon : ℝ)
    (hclose : ‖phi - pi phi‖ ≤ epsilon) :
    ‖rankOneApply phi varphi‖ ^ 2 - ‖pi (rankOneApply phi (pi varphi))‖ ^ 2 ≤
      2 * Real.sqrt 2 * epsilon := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
