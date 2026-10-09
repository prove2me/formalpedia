-- Prove2me | Theorems.Thm_SWPort_Davenport_siegel_walfisz_ap
-- name    : SWPort.Davenport.siegel_walfisz_ap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:23:51.193737+00:00
-- url     : https://prove2.me/theorems/49f1274c-362f-4657-98b2-44f7ce4ae50e
-- title:
--   The Siegel–Walfisz theorem for arithmetic progressions (Davenport §22) (ported to Mathlib 0df444a)
-- statement:
--   **The Siegel–Walfisz theorem, progression form** (Davenport §22). For any fixed $A>0$ there are constants $c,C>0$ such that for all $N\ge2$, all moduli $1\le q\le(\log N)^A$ and all $a$ with $\gcd(a,q)=1$,
--   $$\Bigl|\psi(N;q,a)-\frac{N}{\varphi(q)}\Bigr|\;\le\;C\,N\exp\bigl(-c\sqrt{\log N}\bigr),\qquad \psi(N;q,a)=\sum_{\substack{n<N\\ n\equiv a\ (q)}}\Lambda(n),$$
--   i.e. $\psi(x;q,a)=x/\varphi(q)+O\bigl(x\exp(-C_A(\log x)^{1/2})\bigr)$ uniformly for $q\le(\log x)^A$. It follows from the character form by orthogonality of characters, $\psi(N;q,a)=\varphi(q)^{-1}\sum_{\chi}\overline{\chi}(a)\psi(N,\chi)$. The constants are ineffective.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.siegel_walfisz_ap` (ff9f3207-eba1-492e-9691-e50480292b68, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission c971b7bd-d4d1-4c00-8af0-275aab368880 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68) by alya

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section

namespace SWPort

open Finset

open Classical in
theorem _root_.SWPort.Davenport.siegel_walfisz_ap (A : ℝ) (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N q a : ℕ), 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ A → Nat.Coprime a q →
        |Davenport.psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)|
          ≤ C * N * Real.exp (-c * Real.sqrt (Real.log N)) := by
  sorry

end SWPort
end
