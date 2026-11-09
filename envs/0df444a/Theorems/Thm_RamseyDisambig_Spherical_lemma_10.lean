-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_lemma_10
-- name    : RamseyDisambig.Spherical.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:22:13.557241+00:00
-- url     : https://prove2.me/theorems/0e5e3c38-293b-42a8-bd61-8ad2c8cc33c7
-- title:
--   Lemma 10 — VC-dimension preservation under pullback
-- statement:
--   Let $X,Y$ be arbitrary sets, $\iota_1,\iota_2:Y\to X$ arbitrary maps, and $c:X\times X\to\{0,1\}$ any binary coloring. For an integer $q\ge1$, put $\widehat c(y,y')=c(\iota_1(y),\iota_2(y'))$. Then
--   $$q\le\operatorname{VCdim}(\widehat c)\ \Longrightarrow\ q\le\operatorname{VCdim}(c).$$
--   The statement applies to infinite as well as finite sets and requires neither map to be injective. It connects restrictions of rows and columns with VC-dimension in the ambient matrix.
--
--   Differences from the source:
--   - reading: q ∈ ℕ → q ≥ 1; reason: the paper uses positive integers under the recorded reading
--   - encoding: binary colorings and column VC-dimension → Bool labels with row-first NatureSLT.GrowthFunction.vcDim valued in ℕ∞; reason: these preserve all binary patterns and allow infinite VC-dimension
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 10, p. 10 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_NatureSLT_GrowthFunction_vcDim

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Lemma 10, p. 10. Rows are pulled back along ι₁ and columns along ι₂. -/
theorem lemma_10 {X Y : Type*} (ι₁ ι₂ : Y → X) (c : X → X → Bool)
    (q : ℕ) (hq : 1 ≤ q)
    (hvc : (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim (fun y y' => c (ι₁ y) (ι₂ y'))) :
    (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by sorry

end RamseyDisambig.Spherical
