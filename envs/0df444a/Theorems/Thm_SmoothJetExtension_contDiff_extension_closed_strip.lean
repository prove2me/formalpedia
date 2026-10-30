-- Prove2me | Theorems.Thm_SmoothJetExtension_contDiff_extension_closed_strip
-- name    : SmoothJetExtension.contDiff_extension_closed_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T20:32:01.144136+00:00
-- url     : https://prove2.me/theorems/bc34e8d0-731f-4335-a6f9-017e0ab3a412
-- title:
--   Smooth extension across the endpoints of a closed time strip
-- statement:
--   Let E be a finite-dimensional real normed space and F a real Banach space. Let f be smooth on the closed strip in E times the real line with time in [0,1]. Assume f vanishes outside one fixed compact subset of E, uniformly at every real time. Then there is a globally smooth function H on the product satisfying
--
--   $$H(e,t)=f(e,t)\quad(0\le t\le1).$$
--
--   No support condition is required of H. This supplies a smooth ambient representative for a family given only up to the endpoints of its time interval.
-- source:
--   Derived two-endpoint form of Seeley extension from the proved boundary-jet theorem https://prove2.me/theorems/47b24167-67e2-54e6-bbd4-d892636817a7. Flat zero extension is proved via HasFTaylorSeriesUpToOn and unions of within derivatives. The endpoint extensions are combined with Real.smoothTransition. Application: the exact closed-interval hypotheses of https://prove2.me/theorems/127b6bf7-3a22-4600-82ae-2c5c3205a1bb. Derived lemma, not a verbatim numbered statement of Geiges.

import Mathlib
open Set Function
open scoped ContDiff

theorem SmoothJetExtension.contDiff_extension_closed_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E × ℝ → F) (hf : ContDiffOn ℝ ∞ f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → f p = 0) :
    ∃ H : E × ℝ → F, ContDiff ℝ ∞ H ∧
      EqOn H f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1} := by sorry
