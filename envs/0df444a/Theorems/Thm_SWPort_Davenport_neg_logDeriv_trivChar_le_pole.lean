-- Prove2me | Theorems.Thm_SWPort_Davenport_neg_logDeriv_trivChar_le_pole
-- name    : SWPort.Davenport.neg_logDeriv_trivChar_le_pole
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:19.401292+00:00
-- url     : https://prove2.me/theorems/5000d393-e33a-4df9-b805-5ca91fa3ad14
-- title:
--   $-\operatorname{Re}\,L'/L(s,\chi_0)\le\operatorname{Re}\frac1{s-1}+c\log(q(|t|+2))$ for $1<\sigma\le2$ (Davenport §13–14) (ported to Mathlib 0df444a)
-- statement:
--   **The principal-character bound with the pole term** (Davenport §13 for $\zeta$, §14 for $\chi_0$ mod $q$). There is an absolute constant $c>0$ such that for every modulus $q\ge1$ and every $s=\sigma+it$ with $1<\sigma\le2$,
--   $$\operatorname{Re}\Bigl(-\frac{L'}{L}(s,\chi_0)\Bigr)\;\le\;\operatorname{Re}\frac{1}{s-1}+c\log\bigl(q(|t|+2)\bigr),$$
--   $\chi_0$ the principal character modulo $q$. Since $L(s,\chi_0)=\zeta(s)\prod_{p\mid q}(1-p^{-s})$, one has $-L'/L(s,\chi_0)=-\zeta'/\zeta(s)-\sum_{p\mid q}\frac{(\log p)p^{-s}}{1-p^{-s}}$, and the finite sum has real part at most $\sum_{p\mid q}\log p\le\log q$ in absolute value; the bound $-\operatorname{Re}\zeta'/\zeta(s)\le\operatorname{Re}\frac1{s-1}+c\log(|t|+2)$ is Davenport §13's consequence of the partial-fraction formula for $\zeta'/\zeta$ (§12), every term $-\operatorname{Re}\frac1{s-\rho}$ over the zeros being non-positive for $\sigma>1$. This is the "$\chi^2=\chi_0$" input in the $3$–$4$–$1$ argument for real characters, where the third point $\sigma+2it$ is not on the real axis.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.neg_logDeriv_trivChar_le_pole` (e7d1b484-b924-4238-b7fe-e79d905bd6c1, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 94a9e456-63c4-4b18-9444-65c7969a7dab by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.neg_logDeriv_trivChar_le_pole (e7d1b484-b924-4238-b7fe-e79d905bd6c1) by alya

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

set_option linter.unusedVariables false

open Complex

theorem _root_.SWPort.Davenport.neg_logDeriv_trivChar_le_pole : ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (s : ℂ), 1 < s.re → s.re ≤ 2 →
      (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
          / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)).re
        ≤ (1 / (s - 1)).re + c * Real.log ((q : ℝ) * (|s.im| + 2)) := by
  sorry

end SWPort
end
