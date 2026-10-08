-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
-- name    : TeschlQM.Herglotz.stieltjes_inversion_formula
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T00:28:10.37918+00:00
-- url     : https://prove2.me/theorems/134ff65e-2ca0-4d36-8fb3-05c19988051c
-- title:
--   Stieltjes inversion formula for every finite Borel measure
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$ with Borel transform $F_\mu$. For every $a<b$,
--
--   $$\lim_{\varepsilon\downarrow0}\frac1\pi\int_a^b\operatorname{Im}F_\mu(t+i\varepsilon)\,dt=\frac{\mu((a,b))+\mu([a,b])}{2}.$$
--
--   The formula counts atoms at each endpoint with weight one half. It is stated independently of transform uniqueness so it can be reused directly.
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

theorem TeschlQM.Herglotz.stieltjes_inversion_formula (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) * (∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im))
      (𝓝[>] 0) (𝓝 (((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2)) := by sorry
