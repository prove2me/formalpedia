-- Prove2me | Theorems.Thm_RealPoisson_interval_arctan_mass_tendsto
-- name    : RealPoisson.interval_arctan_mass_tendsto
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T00:27:12.015974+00:00
-- url     : https://prove2.me/theorems/b841b21d-4691-414a-bcbb-0d2de03b4bb6
-- title:
--   Poisson kernel interval masses converge with half-weight endpoint atoms
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$ and $a<b$. Then
--
--   $$\lim_{\varepsilon\downarrow0}\int_{\mathbb R}\frac{\arctan((b-x)/\varepsilon)-\arctan((a-x)/\varepsilon)}{\pi}\,d\mu(x)=\frac{\mu((a,b))+\mu([a,b])}{2}.$$
--
--   The two endpoint atoms receive weight one half. This is the integrated Poisson-kernel limit used in Stieltjes inversion.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), p. 108, Theorem 3.21 and its proof, Eq. (3.89); https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF p. 119).

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

theorem RealPoisson.interval_arctan_mass_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, (Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε)) / Real.pi ∂μ) (𝓝[>] 0)
      (𝓝 (((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2)) := by sorry
