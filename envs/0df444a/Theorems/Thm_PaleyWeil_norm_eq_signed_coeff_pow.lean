-- Prove2me | Theorems.Thm_PaleyWeil_norm_eq_signed_coeff_pow
-- name    : PaleyWeil.norm_eq_signed_coeff_pow
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:19:14.402511+00:00
-- url     : https://prove2.me/theorems/f6302362-3bef-4006-8166-2e59db5f4eea
-- title:
--   Field norm from the minimal polynomial constant coefficient
-- statement:
--   For an element x of a finite-dimensional field extension L/K, write d for the degree of its minimal polynomial. Then Normₗ/ₖ(x) is ((−1)ᵈ·minpolyₖ(x)(0)) raised to the exponent [L:K]/d, the natural-number quotient of the extension degree by d.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/MinpolyNorm.lean lines 8–27; SHA256 1d1644dd8914a2bf3daa80a95ce6633528699ec2b7c3051f38481242e149eaf8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace IntermediateField
end IntermediateField
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial IntermediateField
open PaleyWeil

theorem PaleyWeil.norm_eq_signed_coeff_pow {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      ((-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^
        (Module.finrank K L / (minpoly K x).natDegree) := by sorry
