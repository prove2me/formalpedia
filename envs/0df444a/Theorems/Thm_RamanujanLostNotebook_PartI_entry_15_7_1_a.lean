-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_15_7_1_a
-- name    : RamanujanLostNotebook.PartI.entry_15_7_1_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:22:32.570994+00:00
-- url     : https://prove2.me/theorems/fdde6ca7-ede2-432f-a7ab-eb701d52f144
-- title:
--   Order-fifteen incomplete elliptic integral a
-- statement:
--   F(q)=f(-q)=(q;q)_∞ on the real line, via the approved complex Euler product. For |q|<1 the product has its classical convergent value; it is positive for 0≤q<1. Endpoint q=1 is zero and is used only at a measure-zero integration endpoint. Source (15.2.4), p.329. v(q) in (15.7.1), p.349; distinct from the v of (15.7.30). The defining products converge and their denominator factors are nonzero for 0<q<1; definitions outside that domain are not source values. E(m;a,b)=∫_a^b(1-m sin²φ)^{-1/2}dφ, oriented interval integral. The parameter m is the squared modulus, not the modulus. For m<1 the denominator is strictly positive for every real φ and finite intervals are integrable. For 0<q<e^{−2π/√15}, ∫₀^q F(t)F(t³)F(t⁵)F(t¹⁵)dt equals E(9/25;2 arctan(√[(1−11v−v²)/(1+v−v²)]/√5),2 arctan(1/√5))/5, where v=v₁₅(q). Differs from the printed source: The source does not specify the real increasing branch. We require 0<q<exp(-2π/√15); v turns there. At q=0.55, the unrestricted positive-real-root / principal-angle integral expressions are defined real quantities but unequal: left side 0.33797800712619995044262669134078146237047828570852, right side 0.012172753456950555352418517861648188783013546474845 (item 1, closed by the coordinator on 2026-10-09). This branch restriction is ours; numerical evidence, not a proof.
--
--   **Discrepancy from the printed source.** The source does not specify the real increasing branch. We require 0<q<exp(-2π/√15); v turns there. At q=0.55, the unrestricted positive-real-root / principal-angle integral expressions are defined real quantities but unequal: left side 0.33797800712619995044262669134078146237047828570852, right side 0.012172753456950555352418517861648188783013546474845 (item 1, closed by the coordinator on 2026-10-09). This branch restriction is ours; numerical evidence, not a proof.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 15, Entry 15.7.1, p. 351, eq. (15.7.11).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15Elliptic
import Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15F
import Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15V15
import Definitions.Def_RamanujanLostNotebook_PartI_shared_eulerF
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf
open MeasureTheory

namespace RamanujanLostNotebook.PartI
theorem entry_15_7_1_a (q : ℝ) (hq0 : 0 < q) (hq1 : q < Real.exp (-2 * Real.pi / Real.sqrt 15)) :
    IntervalIntegrable (fun t : ℝ => ch15F t * ch15F (t ^ 3) * ch15F (t ^ 5) * ch15F (t ^ 15)) volume 0 q ∧
    1 * (∫ t in 0..q, ch15F t * ch15F (t ^ 3) * ch15F (t ^ 5) * ch15F (t ^ 15)) = (1 / 5 : ℝ) * ch15Elliptic (9 / 25 : ℝ)
      (2 * Real.arctan (1 / Real.sqrt 5 * Real.sqrt ((1 - 11 * ch15V15 q - ch15V15 q ^ 2) /
        (1 + ch15V15 q - ch15V15 q ^ 2)))) (2 * Real.arctan (1 / Real.sqrt 5)) := by sorry
end RamanujanLostNotebook.PartI
