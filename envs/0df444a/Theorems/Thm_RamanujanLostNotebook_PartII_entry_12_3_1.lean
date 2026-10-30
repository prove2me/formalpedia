-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_12_3_1
-- name    : RamanujanLostNotebook.PartII.entry_12_3_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:27:02.862624+00:00
-- url     : https://prove2.me/theorems/58690a30-b0ea-4619-b9cf-a432ac262f57
-- title:
--   Upper cutoff recovers the coefficient as the nearest integer
-- statement:
--   Let C=1+480∑_{k≥1}k⁷/(e^{2πk}−1). Call μ admissible if it is a positive integer c²+d² with gcd(c,d)=1 (μ=1,2,5,10,13,…). Put W₁(n)=1, W₂(n)=(−1)ⁿ and, for admissible μ≥5, W_μ(n)=∑2cos((ac+bd)·2πn/μ+8 arctan(c/d)), one summand for each coprime pair c>d>0 with c²+d²=μ, where a,b are integers with ad−bc=1 (another choice changes ac+bd by a multiple of μ, so W_μ(n) is well defined). Let T(n,μ)=(2/C)·W_μ(n)·e^{2πn/μ}/μ⁴ for admissible μ and 0 otherwise; all summands belonging to one μ form a single term. Let γ_n be the coefficient of zⁿ in (1−504∑_{k≥1}σ₅(k)z^k)⁻¹, i.e. of q^{2n} in 1/R(q²). Let P=∏(1−p⁻²) over primes p≡1 (mod 4). For 0<ε<1 and n≥2 put u_ε(n)=⌊n(1+ε)/((log n)^{3/2}√P)⌋ and let S(n,k) be the sum of the first k terms T(n,μ) in increasing order of admissible μ. Then for every ε in (0,1) there is N with |γ_n−S(n,u_ε(n))|<1/2 for all n≥N; that is, γ_n is the nearest integer to S(n,u_ε(n)) for all sufficiently large n. Differs from the printed source: Entry 12.1.1 (p.313) takes W_μ(n) from (11.5.5) and (11.5.7); the μ=2 value used there is the one fixed in (11.5.6), p.280, namely W₂(n)=−(−1)ⁿ. We use W₂(n)=+(−1)ⁿ, as in the book’s own statement of the same expansion in Entry 11.10.1, equation (11.10.31), p.306; it is also the value of the weight-eight factor (1+i)⁻⁸=1/16 at the orbit c=d=1. This correction is ours, reconciling two locations in the book; no published erratum is cited. With the printed sign the series cannot equal γ_n: the two versions differ by (−1)ⁿe^{πn}/(4C), and at n=0 the printed-sign sum is below 77/80<1=γ₀ (hand proof from C>2 and |∑_{μ≥5}W_μ(0)μ⁻⁴|≤1/40, not machine checked; an interval-arithmetic enclosure gives 0.8820334918…0.8820334949). Agreement of the corrected series with γ_n (within 2.2e−41 at n=0 by an accelerated lattice sum, relative 4.5e−33 at n=8, both including analytic truncation bounds; rounding not interval-certified) is numerical evidence, not a proof. Differs from the printed source: the braces in u(n), p.322, are not defined in the book; we read them as the floor used for ℓ(n) in (12.2.1) (our choice; the ceiling would add one term, covered by the o(1) tail bound of the proof). The entry says γ_n is defined in (12.2.1), which defines ℓ(n); γ_n is defined in Entry 12.1.1 (an editorial slip, corrected by us).
--
--   **Discrepancy from the printed source.** Differs from the printed source: Entry 12.1.1 (p.313) takes W_μ(n) from (11.5.5) and (11.5.7); the μ=2 value used there is the one fixed in (11.5.6), p.280, namely W₂(n)=−(−1)ⁿ. We use W₂(n)=+(−1)ⁿ, as in the book’s own statement of the same expansion in Entry 11.10.1, equation (11.10.31), p.306; it is also the value of the weight-eight factor (1+i)⁻⁸=1/16 at the orbit c=d=1. This correction is ours, reconciling two locations in the book; no published erratum is cited. With the printed sign the series cannot equal γ_n: the two versions differ by (−1)ⁿe^{πn}/(4C), and at n=0 the printed-sign sum is below 77/80<1=γ₀ (hand proof from C>2 and |∑_{μ≥5}W_μ(0)μ⁻⁴|≤1/40, not machine checked; an interval-arithmetic enclosure gives 0.8820334918…0.8820334949). Agreement of the corrected series with γ_n (within 2.2e−41 at n=0 by an accelerated lattice sum, relative 4.5e−33 at n=8, both including analytic truncation bounds; rounding not interval-certified) is numerical evidence, not a proof. Differs from the printed source: the braces in u(n), p.322, are not defined in the book; we read them as the floor used for ℓ(n) in (12.2.1) (our choice; the ceiling would add one term, covered by the o(1) tail bound of the proof). The entry says γ_n is defined in (12.2.1), which defines ℓ(n); γ_n is defined in Entry 12.1.1 (an editorial slip, corrected by us).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12, Entry 12.3.1, p. 322.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Admissible
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12C
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Count
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Gamma
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Inverse
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12MuCutoff
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Phase
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Prefix
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12PrimeProduct
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Reps
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Sigma5
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Term
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Upper
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12W

namespace RamanujanLostNotebook.PartII
theorem entry_12_3_1 (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(ch12Gamma n : ℝ) - ch12Prefix n (ch12Upper epsilon n)| < (1 / 2 : ℝ) := by sorry
end RamanujanLostNotebook.PartII
