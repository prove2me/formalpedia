-- Prove2me | Theorems.Thm_SWPort_Davenport_psi_char_of_region
-- name    : SWPort.Davenport.psi_char_of_region
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:22:34.7786+00:00
-- url     : https://prove2.me/theorems/5b54cbc4-e957-46aa-a69d-ba8d97fef7f7
-- title:
--   Estimate for $\psi(N,\chi)$ from the zero-free region, with exceptional term (Davenport §20) (ported to Mathlib 0df444a)
-- statement:
--   **The prime number theorem for characters, given the zero-free region** (Davenport §20, character form). Fix a region constant $c>0$. There are constants $c_1,c_2,C>0$ (depending only on $c$) such that for every modulus $q\ge1$, every Dirichlet character $\chi$ modulo $q$, and every exceptional set $E$ for $\chi$ with respect to $c$ (`IsExceptionalSet c χ E`: at most one real zero $\beta\in(0,1)$ of $L(\cdot,\chi)$ in the region, only for quadratic $\chi\ne1$, and no other zeros $s\ne1$ in the region $\operatorname{Re}s\ge1-c/\log(q(|\operatorname{Im}s|+2))$), and every $N\ge2$ with
--   $$q\;\le\;\exp\bigl(c_2\sqrt{\log N}\bigr),$$
--   one has
--   $$\Bigl\|\,\psi(N,\chi)-\delta_\chi N+\sum_{\beta\in E}\frac{N^{\beta}}{\beta}\Bigr\|\;\le\;C\,N\exp\bigl(-c_1\sqrt{\log N}\bigr),$$
--   where $\psi(N,\chi)=\sum_{n<N}\Lambda(n)\chi(n)$ and $\delta_\chi=1$ if $\chi$ is principal, $0$ otherwise. That is, $\psi(N,\chi)=\delta_\chi N-\dfrac{N^{\beta_1}}{\beta_1}+O\bigl(N\exp(-c_1\sqrt{\log N})\bigr)$, the term $-N^{\beta_1}/\beta_1$ being present exactly when $\chi$ has an exceptional zero $\beta_1$.
--
--   The region constant is a parameter so that this milestone is independent of the §14 milestone (which produces a specific $c$ together with a witness $E$ for every $\chi$). For a large $c$ the hypothesis on $E$ may be unsatisfiable for some $\chi$, which makes the statement vacuous there, not false. The principal character is included (main term $N$), so the statement contains the prime number theorem with de la Vallée Poussin error.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.psi_char_of_region` (0b61efc4-9fee-4960-8136-bdc620a7c947, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 80a16960-3bff-41fb-a6ef-fe2ab804c25d by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.psi_char_of_region (0b61efc4-9fee-4960-8136-bdc620a7c947) by alya

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section

namespace SWPort

open Finset DirichletCharacter Vino Davenport

set_option maxHeartbeats 1000000 in
open Classical in
theorem _root_.SWPort.Davenport.psi_char_of_region (c : ℝ) (hc : 0 < c) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (E : Set ℂ),
        IsExceptionalSet c χ E →
        ∀ N : ℕ, 2 ≤ N → (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt (Real.log N)) →
          ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)
              + ∑ᶠ z ∈ E, (N : ℂ) ^ z / z‖
            ≤ C * N * Real.exp (-c₁ * Real.sqrt (Real.log N)) := by
  sorry

end SWPort
end
