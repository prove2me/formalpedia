-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_6_2_1
-- name    : RamanujanLostNotebook.PartI.entry_6_2_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:02:49.354374+00:00
-- url     : https://prove2.me/theorems/cba469fe-e749-4955-9472-511d831b9780
-- title:
--   Alternating three-parameter continued fraction
-- statement:
--   Let (t;q)_n=∏_{k=0}^{n−1}(1−tq^k) and (t;q)_∞=∏_{k≥0}(1−tq^k). Let G(a,b,λ;q)=∑_{n≥0}∏_{k=0}^{n−1}(a+λq^k)q^{n(n+1)/2}/((q;q)_n(−bq;q)_n), and P(a,b,λ;q)=(−bq;q)_∞G(a,b,λ;q). Write U(a,b,λ;q)_n=aq^((n+1)/2)+λq^n for odd n≥1 and bq^(n/2)+λq^n for even n≥1. For numerators u_n and denominators d_n, A_{−1}=1, A_0=d_0, B_{−1}=0, B_0=1 and X_n=d_n X_{n−1}+u_n X_{n−2} for X=A,B. The ordinary fraction is lim A_n/B_n; its reciprocal is lim B_n/A_n. Early poles are permitted but the actual denominator must be nonzero eventually. A regular fraction means that A_n and B_n are never simultaneously zero. On the regular q-disk locus, G(aq,b,λq;q)/G(a,b,λ;q) equals 1/(1+(aq+λq)/(1+(bq+λq²)/(1+⋯))). Exact assumptions: |q| < 1; ∀ k, 1 + b·q^(k + 1) ≠ 0; G a b l q ≠ 0; regularCF (U a b l q) (n ↦ 1). Differs from the printed source: We make the inherited |q|<1 range and finite q-Pochhammer nonvanishing explicit. Our formulation writes the removable numerator as ∏(a+λq^k), including the a=0 specializations the book uses, instead of applying totalized division to −λ/a. Our formulation excludes indeterminate simultaneous-zero finite continuants and requires the displayed q-series quotient denominator to be nonzero; convergence and eventual definedness remain conclusions. Independent pre-compile audit: Ratio orientation, alternating numerators, and convergence conclusion agree; residual ≤ 1.83e-110.
--
--   **Discrepancy from the printed source.** We make the inherited |q|<1 range and finite q-Pochhammer nonvanishing explicit. Our formulation writes the removable numerator as ∏(a+λq^k), including the a=0 specializations the book uses, instead of applying totalized division to −λ/a. Our formulation excludes indeterminate simultaneous-zero finite continuants and requires the displayed q-series quotient denominator to be nonzero; convergence and eventual definedness remain conclusions. Independent pre-compile audit: Ratio orientation, alternating numerators, and convergence conclusion agree; residual ≤ 1.83e-110.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6, Entry 6.2.1, p. 144, eq. (6.2.2).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Continuants
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6G
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6HasCF
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6MainNum
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6RegularCF
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Term
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

namespace RamanujanLostNotebook.PartI
theorem entry_6_2_1 (a b l q : ℂ) (hq : ‖q‖ < 1) (hb : ∀ k : ℕ, 1 + b * q ^ (k + 1) ≠ 0) (hG : ch6G a b l q ≠ 0) (hreg : ch6RegularCF (ch6MainNum a b l q) (fun _ => 1)) :
    Summable (ch6Term a b l q) ∧
    Summable (ch6Term (a * q) b (l * q) q) ∧
    ch6HasCF true 1 (ch6MainNum a b l q) (fun _ => 1) (ch6G (a * q) b (l * q) q / ch6G a b l q) := by sorry
end RamanujanLostNotebook.PartI
