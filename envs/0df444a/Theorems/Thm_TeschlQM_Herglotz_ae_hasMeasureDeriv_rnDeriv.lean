-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_ae_hasMeasureDeriv_rnDeriv
-- name    : TeschlQM.Herglotz.ae_hasMeasureDeriv_rnDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:09:38.573177+00:00
-- url     : https://prove2.me/theorems/9d80202a-808a-4847-900e-4d89c91f1c17
-- title:
--   Symmetric-ball derivatives equal the Radon–Nikodym density Lebesgue-a.e.
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$ and let $f=d\mu_{ac}/d\lambda$ be its Radon–Nikodym density relative to Lebesgue measure. Then
--
--   $$\lim_{r\downarrow0}\frac{\mu((t-r,t+r))}{2r}=f(t)\quad\text{for Lebesgue-almost every }t.$$
--
--   The limit is taken in $[0,\infty]$. This is the one-dimensional open-ball form of Theorem A.37 and applies to measures with atoms or singular continuous parts.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), Theorems A.37–A.38, p. 286, Lemma A.39, p. 287, and Theorems 3.22–3.23, pp. 108–109; https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF pp. 119–120, 297–298).

import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Definitions.Def_TeschlQM_Herglotz_acPart

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem TeschlQM.Herglotz.ae_hasMeasureDeriv_rnDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t ∂(volume : Measure ℝ), HasMeasureDeriv μ t (μ.rnDeriv volume t) := by sorry
