-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_count_from_finite_certificate
-- name    : TaoFivePrimes.rh_batch01_height_count_from_finite_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:50:02.024036+00:00
-- url     : https://prove2.me/theorems/b6bb62a0-fc72-461a-a8c6-7a8c337640e8
-- title:
--   TaoFivePrimes.rh_batch01_height_count_from_finite_certificate
-- statement:
--   Soundness of the existing finite contour certificate format for the exact128-unit window. Given ordinary kernel-guarded cell records that enumerate the8448 cells, an oriented-logarithm bound, actual1e-12 polynomial jet enclosures and actual1e-14 Fourier coefficient enclosures, proves at most409 distinct zeros. Includes all analytic steps: continuous nonvanishing, mesh integration, logarithm rounding, strip transfer, rectangle comparison, removal of nonzero factors, completed-zeta argument principle and multiplicity. All numerical and analytic hypotheses are explicit; none is supplied by an axiom or unchecked computation.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourArithmeticV2
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
import Definitions.Def_TaoFivePrimes_RHBatch01ContourGeometry
import Definitions.Def_TaoFivePrimes_RHBatch01CoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
open scoped FourierTransform

theorem TaoFivePrimes.rh_batch01_height_count_from_finite_certificate
 (rs : List RHBatch01ContourArithmeticV2.Record) (d : RHBatch01ContourArithmeticV2.Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=>decide
  (p.1.edge=(if p.2<4096 then 0 else if p.2<4224 then 1 else if p.2<8320 then 2 else 3) ∧
   p.1.index=(if p.2<4096 then p.2 else if p.2<4224 then p.2-4096 else if p.2<8320 then p.2-4224 else p.2-8320)))=true)
 (hs:(rs.map (fun r=>if r.edge<2 then r.log128.2 else -r.log128.2)).sum≤2571*(2:Int)^128)
 (hjet:∀e j k:Nat,e<4 → j≤RHBatch01ContourGeometry.cells e → k<8 →
  ‖RHBatch01PolynomialJet.jet (RHBatch01ContourGeometry.point e j) (RHBatch01ContourGeometry.step e) k-
   RHHighContourVector.value (RHBatch01ContourGridV2.jet e j k)‖≤1/10^12)
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHBatch01FullCoefficient.W ((m:ℝ)/512)-RHBatch01FourierPolynomial.coefficient m‖≤1/10^14) :
 (RHHighHeight.windowZeros 3289999744 3289999872).ncard≤409 := by sorry
