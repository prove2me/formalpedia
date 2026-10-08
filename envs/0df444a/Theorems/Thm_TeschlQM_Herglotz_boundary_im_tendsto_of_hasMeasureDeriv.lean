-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_boundary_im_tendsto_of_hasMeasureDeriv
-- name    : TeschlQM.Herglotz.boundary_im_tendsto_of_hasMeasureDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:02:38.356392+00:00
-- url     : https://prove2.me/theorems/d994fd7c-d719-4249-8645-ad370e944f61
-- title:
--   Poisson boundary values converge at every point with a measure derivative
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$ and $F_\mu$ its Borel transform. If the symmetric-ball derivative of $\mu$ at $t$ exists and equals $d\in[0,\infty]$, then
--
--   $$\lim_{\varepsilon\downarrow0}\frac{\operatorname{Im}F_\mu(t+i\varepsilon)}{\pi}=d.$$
--
--   Infinite derivatives are allowed. This is the pointwise consequence of the lower and upper comparison in Theorem 3.22.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), Theorems A.37–A.38, p. 286, Lemma A.39, p. 287, and Theorems 3.22–3.23, pp. 108–109; https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF pp. 119–120, 297–298).

import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Theorems.Thm_TeschlQM_Herglotz_deriv_le_boundary_im

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem TeschlQM.Herglotz.boundary_im_tendsto_of_hasMeasureDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) (d : ℝ≥0∞)
    (hd : HasMeasureDeriv μ t d) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal
      ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi))
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by sorry
