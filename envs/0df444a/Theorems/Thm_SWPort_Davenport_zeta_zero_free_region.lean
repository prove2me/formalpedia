-- Prove2me | Theorems.Thm_SWPort_Davenport_zeta_zero_free_region
-- name    : SWPort.Davenport.zeta_zero_free_region
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:19.621589+00:00
-- url     : https://prove2.me/theorems/f054cd95-77a2-429b-8dc8-31b38c607856
-- title:
--   The classical zero-free region for $\zeta$: $\zeta(s)\ne0$ for $\sigma\ge1-c/\log(|t|+2)$ (Davenport §13) (ported to Mathlib 0df444a)
-- statement:
--   **The de la Vallée Poussin zero-free region for the Riemann zeta function** (Davenport §13). There is an absolute constant $c>0$ such that
--   $$\zeta(s)\neq0\qquad\text{whenever}\qquad s\neq1\ \text{ and }\ \operatorname{Re}s\;\ge\;1-\frac{c}{\log(|\operatorname{Im}s|+2)} .$$
--   Here $\zeta$ is Mathlib's analytically continued Riemann zeta function (its value at the pole $s=1$ is excluded). Davenport proves it from the $3$–$4$–$1$ inequality for $-\zeta'/\zeta$ and the partial-fraction bound $-\operatorname{Re}\zeta'/\zeta(s)<c\log|t|-\operatorname{Re}\frac1{s-\rho}$ for $1\le\sigma\le2$, $|t|\ge2$; near the real axis the region is zero-free because $\zeta(s)\neq0$ on $\operatorname{Re}s\ge1$ (Mathlib) and $\zeta$ has no zeros in a neighbourhood of the compact set $\{\sigma\ge1-\varepsilon, |t|\le2\}$ apart from the pole. It is the $q=1$ (principal character) case of the zero-free region for $L(s,\chi)$ and the input for the prime number theorem with error term $O(x\exp(-c\sqrt{\log x}))$ (§18).
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.zeta_zero_free_region` (0dba2dc9-e9a0-442a-ad71-dc6eefb8c001, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 4c05d6ff-50fe-4193-9977-f98fe6f65d93 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.zeta_zero_free_region (0dba2dc9-e9a0-442a-ad71-dc6eefb8c001) by alya

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

set_option linter.unusedVariables false

open Complex

theorem _root_.SWPort.Davenport.zeta_zero_free_region : ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0 := by
  sorry

end SWPort
end
