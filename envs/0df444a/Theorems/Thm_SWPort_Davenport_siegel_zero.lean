-- Prove2me | Theorems.Thm_SWPort_Davenport_siegel_zero
-- name    : SWPort.Davenport.siegel_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:20.832121+00:00
-- url     : https://prove2.me/theorems/703d9f34-e4b4-4bcb-9450-6a3b28aa0d64
-- title:
--   Siegel's theorem, second form: no real zero of $L(s,\chi)$ in $\sigma > 1 - C(\varepsilon)q^{-\varepsilon}$ (Davenport §21) (ported to Mathlib 0df444a)
-- statement:
--   **Siegel's theorem, second form** (Davenport §21): for any $\varepsilon>0$ there exists $C(\varepsilon)>0$ such that, if $\chi$ is a real primitive character to the modulus $q$, then
--   $$L(\sigma,\chi)\;\neq\;0\qquad\text{for all real }\sigma>1-C(\varepsilon)\,q^{-\varepsilon};$$
--   equivalently, any real zero $\beta_1$ of $L(s,\chi)$ satisfies $\beta_1\le1-C(\varepsilon)q^{-\varepsilon}$. Formally, for every $\varepsilon>0$ there is $C>0$ such that for all $q\ge1$, all quadratic non-principal primitive $\chi$ mod $q$ and all real $\sigma>1-Cq^{-\varepsilon}$, $L(\sigma,\chi)\neq0$. The constant is ineffective. This is the form used in §22 to absorb the exceptional term $N^{\beta_1}/\beta_1$ of the §20 estimate.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.siegel_zero` (93f232fb-3b80-4868-a4ce-95e1194e5e22, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission d5e989ba-7e0e-4db1-b291-3d73dd5b9984 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.siegel_zero (93f232fb-3b80-4868-a4ce-95e1194e5e22) by alya

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

open Finset DirichletCharacter

theorem _root_.SWPort.Davenport.siegel_zero (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          ∀ σ : ℝ, 1 - C * (q : ℝ) ^ (-ε) < σ →
            DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  sorry

end SWPort
end
