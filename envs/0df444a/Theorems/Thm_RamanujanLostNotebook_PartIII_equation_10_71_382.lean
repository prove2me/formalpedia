-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_equation_10_71_382
-- name    : RamanujanLostNotebook.PartIII.equation_10_71_382
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T12:47:11.164741+00:00
-- url     : https://prove2.me/theorems/2d4219b4-5c73-42d9-9365-1d3102e54c55
-- title:
--   Divisor maximal order at one
-- statement:
--   Sigma_{−1}(x)/exp(gamma) is loglog x−2(sqrt2−1)/sqrt(log x)+S_1(log x), with error O(1/(sqrt(log x)loglog x)). Differs from the printed source: maximum order is represented by the continuous superior envelope, as clarified by the editors on p.394; the infimum of supporting power curves also defines the values between champion integers.
--
--   **Discrepancy from the printed source.** Differs from the printed source: maximum order is represented by the continuous superior envelope, as clarified by the editors on p.394; the infimum of supporting power curves also defines the values between champion integers.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10, Section 10.71, p. 386, eq. (10.71.382).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Champion
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Envelope
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Exponent
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10LocalRatio
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Primes
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10RH
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Sigma
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Threshold
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroOrder
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroS__4d5713
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroSum
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Zeros
open scoped BigOperators Topology
open MeasureTheory

namespace RamanujanLostNotebook.PartIII
theorem equation_10_71_382 (hRH : ch10RH) :
    Asymptotics.IsBigO Filter.atTop (fun x : ℝ => ch10Envelope 1 x / Real.exp Real.eulerMascheroniConstant - Real.log (Real.log x) + 2 * (Real.sqrt 2 - 1) / Real.sqrt (Real.log x) - ch10ZeroS 1 (Real.log x)) (fun x : ℝ => 1 / (Real.sqrt (Real.log x) * Real.log (Real.log x))) := by sorry
end RamanujanLostNotebook.PartIII
