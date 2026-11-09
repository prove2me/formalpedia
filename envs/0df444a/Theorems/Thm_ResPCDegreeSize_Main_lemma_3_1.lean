-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_lemma_3_1
-- name    : ResPCDegreeSize.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:03.373899+00:00
-- url     : https://prove2.me/theorems/aee2303c-770a-4490-9eb2-f31886448888
-- title:
--   Lemma 3.1 — rank specialization
-- statement:
--   Let $M_1,\dots,M_s$ be matrices over $\mathbb F_p$ of the same dimensions. For algebraically independent indeterminates $\lambda_1,\dots,\lambda_s$ put
--   $$M(\lambda)=\sum_{i=1}^s\lambda_iM_i,\qquad R=\operatorname{rank}_{\mathbb F_p(\lambda)}M(\lambda).$$
--   Then the average rank over the $p^s$ points $a\in\mathbb F_p^s$ satisfies
--   $$\mathbb E_{a\in\mathbb F_p^s}\bigl[\operatorname{rank}M(a)\bigr]\ge\Bigl(1-\frac1p\Bigr)R.$$
--
--   Specializing a generic linear combination at a uniform point of $\mathbb F_p^s$ therefore keeps a $(1-1/p)$ fraction of the rank on average.
--
--   Differences from the source:
--   - encoding: F_p(λ) with algebraically independent λ_i → the fraction field of MvPolynomial (Fin s) (ZMod p) and the images of its variables; reason: the λ_i are then algebraically independent, and any algebraically independent family generates an isomorphic field
--   - encoding: the expectation over a ∈ F_p^s → the sum over all a divided by p^s, as a real number; reason: this is the uniform average
--   - encoding: matrices over F_p of the same dimensions → Matrix (Fin a) (Fin b) (ZMod p) with [Fact p.Prime]; reason: relabelling of rows and columns; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Lemma 3.1, eq. (14), PDF p. 5 (printed p. 4)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem lemma_3_1 {p s a b : ℕ} [Fact p.Prime] (M : Fin s → Matrix (Fin a) (Fin b) (ZMod p)) :
    (1 - 1 / (p : ℝ)) * ((matLam M).rank : ℝ) ≤
      (∑ c : Fin s → ZMod p, ((∑ i, c i • M i).rank : ℝ)) / (p : ℝ) ^ s := by sorry

end ResPCDegreeSize.Main
