-- Prove2me | Theorems.Thm_SWPort_Davenport_zero_free_region
-- name    : SWPort.Davenport.zero_free_region
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:22:30.55962+00:00
-- url     : https://prove2.me/theorems/cf5fec90-27e4-4617-a6fe-2dd0eef76a4d
-- title:
--   Zero-free region for $L(s,\chi)$ with at most one exceptional real zero (Davenport §14) (ported to Mathlib 0df444a)
-- statement:
--   **Zero-free region for Dirichlet $L$-functions** (Davenport §14). There is an absolute constant $c>0$ such that for every modulus $q\ge1$ and every Dirichlet character $\chi$ modulo $q$, the function $L(s,\chi)$ has no zero $s\neq1$ in the region
--   $$\operatorname{Re}s\;\ge\;1-\frac{c}{\log\bigl(q(|\operatorname{Im}s|+2)\bigr)},$$
--   with at most **one** exception: the exceptional zero, if it exists, is real, lies in $(0,1)$, is **simple** ($L'(\beta,\chi)\neq0$), and can occur only when $\chi$ is a real (quadratic) non-principal character.
--
--   Formally: there is $c>0$ such that for all $q\ge1$ and all $\chi$ mod $q$ there is a set $E$ with `IsExceptionalSet c χ E` (see the definition file: $E$ has at most one element, its elements are real zeros in $(0,1)$ inside the region, only for quadratic $\chi\ne1$, and $L(s,\chi)\ne0$ on the region away from $E$ and from $s=1$) and $L'(z,\chi)\neq0$ for every $z\in E$. The point $s=1$ is exempted because $L(s,\chi_0)$ has a pole there; for $\chi\neq\chi_0$ nonvanishing at $s=1$ is already in Mathlib. The constant $c$ is effective; only the *existence* of a suitable $c$ is asserted.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.zero_free_region` (deb21296-41c0-4d78-90cb-dd1682f5a433, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 2c2d28d0-8283-4d74-8ae6-8838d91c9fdf by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.zero_free_region (deb21296-41c0-4d78-90cb-dd1682f5a433) by alya

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section

namespace SWPort

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset DirichletCharacter Vino

theorem _root_.SWPort.Davenport.zero_free_region :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        ∃ E : Set ℂ, Davenport.IsExceptionalSet c χ E ∧
          ∀ z ∈ E, deriv (DirichletCharacter.LFunction χ) z ≠ 0 := by
  sorry

end SWPort
end
