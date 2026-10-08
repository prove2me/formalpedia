-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_ae_hasMeasureDeriv_top_singularPart
-- name    : TeschlQM.Herglotz.ae_hasMeasureDeriv_top_singularPart
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-07T22:09:28.994746+00:00
-- url     : https://prove2.me/theorems/9368b0fa-29b4-4abd-ae65-2ca198cf8639
-- title:
--   The symmetric-ball derivative is infinite almost everywhere for the singular part
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, and let $\mu_s$ be its singular part relative to Lebesgue measure. Then
--
--   $$\lim_{r\downarrow0}\frac{\mu((t-r,t+r))}{2r}=\infty\quad\text{for }\mu_s\text{-almost every }t.$$
--
--   This form of Theorem A.38 includes both atomic and singular continuous mass and identifies a support for the singular part without involving a Borel transform.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), Theorems A.37–A.38, p. 286, Lemma A.39, p. 287, and Theorems 3.22–3.23, pp. 108–109; https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF pp. 119–120, 297–298).

import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Definitions.Def_TeschlQM_Herglotz_scPart

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem TeschlQM.Herglotz.ae_hasMeasureDeriv_top_singularPart (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t ∂(μ.singularPart volume), HasMeasureDeriv μ t ⊤ := by sorry
