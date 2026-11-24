-- Prove2me | Theorems.Thm_PaleyWeil_splitLPrimeSum_eq_extension_sum
-- name    : PaleyWeil.splitLPrimeSum_eq_extension_sum
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:29.609638+00:00
-- url     : https://prove2.me/theorems/ec81e820-9e6d-4d0b-896b-e9dfa1a2b273
-- title:
--   Prime-polynomial sums equal extension-field character sums
-- statement:
--   Let L/K be a finite extension of finite fields of odd characteristic, let n = [L:K], and let s be a finite set in K. The degree-n prime-polynomial sum splitLPrimeSum(s,n) equals Σₓ∈L χₗ(∏ₐ∈s(x − a)), with each a embedded into L.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PrimeExtensionIdentity.lean lines 46–88; SHA256 d113fc031d5c0aa614a4c357fd5a39717c8a6dce25abc901f9462b7d82a891fe; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
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

theorem PaleyWeil.splitLPrimeSum_eq_extension_sum {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (s : Finset K) :
    splitLPrimeSum s (Module.finrank K L) =
      ∑ x : L, quadraticChar L (∏ a ∈ s, (x - algebraMap K L a)) := by sorry
