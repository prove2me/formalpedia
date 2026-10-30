-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_7_3_1_expansion
-- name    : RamanujanLostNotebook.PartI.entry_7_3_1_expansion
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T05:09:43.285731+00:00
-- url     : https://prove2.me/theorems/7c1da23d-9896-4350-b37b-6be887f46c20
-- title:
--   Continued fraction with all-orders even expansion
-- statement:
--   For x>0, the continued fraction with negative unit numerators and denominators 1+e^{nx} converges. Multiplying its value by (3x)^{1/3} gives Γ(1/3)/Γ(2/3) exp(G(x)). The normalized G has all even coefficients prescribed by (7.2.3), with every fixed prefix remainder o(x^(2N)). Here k=3 and χ has residue values 0,1,−1 modulo 3. Here a_ν=4Γ(ν)ζ(ν)L(ν+1,χ)/(2π/√k)^{2ν+1}, ζ(s)=∑_{n≥1}n^{-s}, and L(s,χ)=∑_{n≥1}χ(n)n^{-s} in increasing-index order; the implementation groups complete periods at s=1. Write P(x)=∏_{r=1}^{k−1}(e^{−rx};e^{−kx})∞^{−χ(r)}, M_j=∑_{r=1}^{k−1}χ(r)r^j, and G(x)=log P(x)−(M₁/k)log(kx)−∑_{r=1}^{k−1}χ(r)log Γ(r/k).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7, Entry 7.3.1, p. 188, eq. (7.3.7).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07CFConverges
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Chi3
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Coefficient
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Continuants
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Convergent
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07L
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07LTerm
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07MinusDenominator
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07MinusNumerator
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Moment
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07OddG
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Poch
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07PochConverges
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Product
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Zeta
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf
open Filter Asymptotics

namespace RamanujanLostNotebook.PartI
theorem entry_7_3_1_expansion :
    (∀ x : ℝ, 0 < x → ch07PochConverges 3 x ∧
      ch07CFConverges ch07MinusNumerator (ch07MinusDenominator 3 x)
        (((Real.Gamma (1 / 3 : ℝ) / Real.Gamma (2 / 3 : ℝ)) * Real.exp (ch07OddG 3 ch07Chi3 x) /
          (Real.rpow (3 * x) (1 / 3 : ℝ)) : ℝ) : ℂ)) ∧
    ∀ N : ℕ, 1 ≤ N →
      (fun x : ℝ => ch07OddG 3 ch07Chi3 x -
        ∑ n ∈ Finset.Icc 1 N, ch07Coefficient 3 ch07Chi3 (2 * n) * x ^ (2 * n))
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (2 * N)) := by sorry
end RamanujanLostNotebook.PartI
