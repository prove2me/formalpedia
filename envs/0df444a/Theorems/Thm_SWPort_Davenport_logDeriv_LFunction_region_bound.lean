-- Prove2me | Theorems.Thm_SWPort_Davenport_logDeriv_LFunction_region_bound
-- name    : SWPort.Davenport.logDeriv_LFunction_region_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:22:58.937504+00:00
-- url     : https://prove2.me/theorems/884918dd-54a9-4609-8b7d-ed4b88d38526
-- title:
--   $L'/L(s,\chi)\ll\log^2 q(|t|+2)$ in the zero-free region, after removing the poles at $1$ and at the exceptional zero (Davenport §§16, 19) (ported to Mathlib 0df444a)
-- statement:
--   **The logarithmic derivative of $L(s,\chi)$ is $O(\log^2 q(|t|+2))$ in a zero-free region, once its polar parts are removed.** Fix a region constant $c>0$. There is a constant $C>0$, depending only on $c$, such that for every modulus $q\ge1$, every Dirichlet character $\chi$ modulo $q$ and every exceptional set $E$ for $\chi$ with respect to $c$ (`IsExceptionalSet c χ E`: $E$ has at most one element; each element is a real zero $\beta\in(0,1)$ of $L(\cdot,\chi)$ lying in the region $\sigma\ge1-c/\log(q(|t|+2))$, and can exist only if $\chi$ is quadratic and non-principal; and $L(s,\chi)\ne0$ at every $s\ne1$ of that region outside $E$) the following two statements hold.
--
--   1. **The exceptional zero has small multiplicity:** for every $\beta\in E$, the order $m_\beta$ of the zero of $L(\cdot,\chi)$ at $\beta$ satisfies $m_\beta\le C\log(2q)$.
--
--   2. **Bound in the quarter-region.** For every complex $s=\sigma+it$ with
--   $$\sigma\;\ge\;1-\frac{c/4}{\log\bigl(q(|t|+2)\bigr)},\qquad \sigma\ge\tfrac34,\qquad s\ne1,\qquad s\notin E,$$
--   one has
--   $$\Bigl|\;\frac{L'}{L}(s,\chi)\;+\;\frac{\delta_\chi}{s-1}\;-\;\sum_{\beta\in E}\frac{m_\beta}{s-\beta}\;\Bigr|\;\le\;C\,\log^2\bigl(q(|t|+2)\bigr),$$
--   where $\delta_\chi=1$ if $\chi$ is the principal character and $\delta_\chi=0$ otherwise.
--
--   In words: inside the (slightly shrunken) zero-free region, $L'/L(s,\chi)$ equals the sum of its polar parts — $-1/(s-1)$ from the pole of $L(s,\chi_0)$ at $s=1$, and $m_\beta/(s-\beta)$ from the exceptional zero — plus a remainder that is uniformly $O(\log^2 q(|t|+2))$. This is the estimate Davenport uses in §§19–20 for the integrals over the shifted contour: it comes from the local partial-fraction expansion $\frac{L'}{L}(s,\chi)=\sum_{|\rho-s_0|\le3/2}\frac{m_\rho}{s-\rho}+O(\log q(|t|+2))$ (§16), since every zero other than $\beta$ lies outside the region, so $|s-\rho|\gg1/\log q(|t|+2)$ for $s$ in the quarter-region, and there are only $O(\log q(|t|+2))$ such $\rho$. For the principal character one uses $L(s,\chi_0)=\zeta(s)\prod_{p\mid q}(1-p^{-s})$, whose finite product contributes $O(\log q)$ to the logarithmic derivative for $\sigma\ge3/4$, and the corresponding bound for $\zeta'/\zeta+1/(s-1)$ in a zero-free region of $\zeta$.
--
--   The region constant is a free parameter (as in `Davenport.psi_char_of_region`) so that the theorem is independent of the specific constant produced by the §14 zero-free-region theorem; for large $c$ the hypothesis may be unsatisfiable, which makes the statement vacuous there, not false. The restriction $\sigma\ge3/4$ keeps everything inside the half-plane where the growth bound $L(s,\chi)\ll q|s|$ and the partial-fraction expansion are available without the functional equation; the contour arguments of §§19–20 only ever use $\sigma\ge 1-c'/\log(qT)$ with $c'$ small.
--
--   **Formalization Note.** `InRegion (c/4) q s` unfolds to $1-\frac{c/4}{\log(q(|\operatorname{Im}s|+2))}\le\operatorname{Re}s$; `analyticOrderNatAt (LFunction χ) z` is the order $m_z$ of the zero; the sum over $E$ is a finite sum over the (at most one-element) set $E$ (`∑ᶠ`); the `if χ = 1 then 1/(s-1) else 0` term is $\delta_\chi/(s-1)$. Both conclusions are stated with a single constant $C$ for convenience.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.logDeriv_LFunction_region_bound` (73d46b4d-209f-401a-8246-602afd9fb331, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission f1fce16d-1a30-461d-a96e-16ad52a62509 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.logDeriv_LFunction_region_bound (73d46b4d-209f-401a-8246-602afd9fb331) by alya

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section

namespace SWPort

open Finset DirichletCharacter Vino Davenport

set_option maxHeartbeats 2000000 in
open Classical in
theorem _root_.SWPort.Davenport.logDeriv_LFunction_region_bound (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (E : Set ℂ),
        IsExceptionalSet c χ E →
          (∀ z ∈ E, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)
              ≤ C * Real.log (2 * q)) ∧
          ∀ s : ℂ, InRegion (c / 4) q s → 3 / 4 ≤ s.re → s ≠ 1 → s ∉ E →
            ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
                + (if χ = 1 then 1 / (s - 1) else 0)
                - ∑ᶠ z ∈ E, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
              ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
  sorry

end SWPort
end
