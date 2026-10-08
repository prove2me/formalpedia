-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_borelTransform_im
-- name    : TeschlQM.Herglotz.borelTransform_im
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T00:27:33.965587+00:00
-- url     : https://prove2.me/theorems/a6618547-b671-48b9-b882-9cebf35b779d
-- title:
--   Imaginary part of a finite-measure Borel transform is its Poisson integral
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, $t\in\mathbb R$ and $\varepsilon>0$. Its Borel transform satisfies
--
--   $$\operatorname{Im}F_\mu(t+i\varepsilon)=\int_{\mathbb R}\frac{\varepsilon}{(x-t)^2+\varepsilon^2}\,d\mu(x).$$
--
--   This identifies the boundary imaginary part with the upper half-plane Poisson kernel before the normalization by $1/\pi$.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), p. 108, Theorem 3.21 and its proof, Eq. (3.89); https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF p. 119).

import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

theorem TeschlQM.Herglotz.borelTransform_im (μ : Measure ℝ) [IsFiniteMeasure μ] (t ε : ℝ) (hε : 0 < ε) :
    (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im =
      ∫ x : ℝ, ε / ((x - t)^2 + ε^2) ∂μ := by sorry
