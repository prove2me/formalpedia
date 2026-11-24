-- Prove2me | Theorems.Thm_PaleyWeil_mem_minpoly_image_iff
-- name    : PaleyWeil.mem_minpoly_image_iff
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:34:15.464076+00:00
-- url     : https://prove2.me/theorems/6476cfd2-6ba6-46f7-9c6c-08f54d3ab9fe
-- title:
--   Minimal polynomials occurring in a finite-field extension
-- statement:
--   For a finite extension L/K of finite fields, a polynomial P over K is the minimal polynomial of some element of L if and only if P is monic and irreducible and its degree divides [L:K].
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PrimeExtensionIdentity.lean lines 7–44; SHA256 d113fc031d5c0aa614a4c357fd5a39717c8a6dce25abc901f9462b7d82a891fe; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem PaleyWeil.mem_minpoly_image_iff {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L] (P : K[X]) :
    P ∈ (Finset.univ.image (minpoly K : L → K[X])) ↔
      P.Monic ∧ Irreducible P ∧ P.natDegree ∣ Module.finrank K L := by sorry
