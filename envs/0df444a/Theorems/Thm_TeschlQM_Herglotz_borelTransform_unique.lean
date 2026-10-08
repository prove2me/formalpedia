-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_borelTransform_unique
-- name    : TeschlQM.Herglotz.borelTransform_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T00:28:12.293543+00:00
-- url     : https://prove2.me/theorems/26d61251-f123-4712-bd97-6e1e4d8d81a3
-- title:
--   A finite Borel measure is uniquely determined by its transform on the upper half-plane
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$. If
--
--   $$F_\mu(z)=F_\nu(z)\qquad(\operatorname{Im}z>0),$$
--
--   then $\mu=\nu$. Equality is required only on the open upper half-plane; both measures may have atoms and singular parts.
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

theorem TeschlQM.Herglotz.borelTransform_unique (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im →
      TeschlQM.Herglotz.borelTransform μ z = TeschlQM.Herglotz.borelTransform ν z) : μ = ν := by sorry
