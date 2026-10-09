-- Prove2me | Theorems.Thm_SWPort_Davenport_logDeriv_LFunction_partial_fraction
-- name    : SWPort.Davenport.logDeriv_LFunction_partial_fraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:24.077916+00:00
-- url     : https://prove2.me/theorems/d5a79704-2d17-4acd-bf91-80ec20436839
-- title:
--   Local partial-fraction expansion of $L'/L(s,\chi)$ with error $O(\log q(|t|+2))$ (Davenport §16) (ported to Mathlib 0df444a)
-- statement:
--   **Partial fractions for the logarithmic derivative of $L(s,\chi)$, locally near the line $\sigma=2$.** There is an absolute constant $C>0$ such that for every modulus $q\ge1$, every non-principal Dirichlet character $\chi$ modulo $q$ and every real height $t$, writing $s_0=2+it$, there is a finite set $Z$ of complex numbers such that:
--
--   1. $Z$ is exactly the set of zeros of $L(s,\chi)$ in the closed disc $|s-s_0|\le 3/2$;
--
--   2. counted with multiplicity, these zeros are few:
--   $$\sum_{\rho\in Z} m_\rho\;\le\;C\log\bigl(q(|t|+2)\bigr),$$
--   where $m_\rho$ is the order of the zero $\rho$;
--
--   3. on the smaller closed disc $|s-s_0|\le 7/5$, at every point where $L(s,\chi)\ne0$,
--   $$\Bigl|\frac{L'}{L}(s,\chi)-\sum_{\rho\in Z}\frac{m_\rho}{s-\rho}\Bigr|\;\le\;C\log\bigl(q(|t|+2)\bigr).$$
--
--   This is the $L$-function analogue of Landau's local form of the Hadamard-product expansion of $\zeta'/\zeta$ (the platform theorem `Zeta23.WeilEF.zeta_logDeriv_partial_fraction`), and is the form in which Davenport's §16 formula $\frac{L'}{L}(s,\chi)=\sum_{|\gamma-t|<1}\frac1{s-\rho}+O(\log q(|t|+2))$ is used in §§14, 19, 20: since the disc $|s-s_0|\le7/5$ covers the whole strip $3/5\le\sigma\le2$ at height $\approx t$, it gives at once (a) the zero-free-region inequality $-\operatorname{Re}\frac{L'}{L}(s,\chi)\le C\log q(|t|+2)-\sum_\rho\operatorname{Re}\frac1{s-\rho}$ for $1<\sigma\le2$ (`Davenport.neg_logDeriv_LFunction_le_sum_zeros`), and (b) the bound $\frac{L'}{L}(s,\chi)\ll\log^2 q(|t|+2)$ inside a zero-free region, which drives the explicit-formula and contour estimates for $\psi(x,\chi)$. It follows from the Borel–Carathéodory / Jensen argument applied to $L(\cdot,\chi)$ on the disc $|s-s_0|\le 75/44$, using the growth bound $|L(s,\chi)|\ll q|s|$ for $\sigma\ge 1/3$ (partial summation) and the lower bound $|L(2+it,\chi)|\ge\zeta(4)/\zeta(2)$ (Euler product); for imprimitive $\chi$ the finitely many Euler factors $1-\chi^*(p)p^{-s}$ contribute $O(\log q)$ to $L'/L$ and have no zeros in the disc.
--
--   **Formalization Note.** `logDeriv f s` is Mathlib's `deriv f s / f s`; `analyticOrderNatAt (LFunction χ) ρ` is the order of the zero at $\rho$; $Z$ is a `Finset ℂ` whose underlying set is specified exactly (clause 1), so the sum in clause 3 ranges over *all* zeros in the disc of radius $3/2$, with the correct multiplicities.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.logDeriv_LFunction_partial_fraction` (4953c8b0-1e84-4fc0-bbdf-aa2bf1843a47, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 318189c3-ca52-46c8-9f38-395a68078ec1 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.logDeriv_LFunction_partial_fraction (4953c8b0-1e84-4fc0-bbdf-aa2bf1843a47) by alya

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

open Finset MeasureTheory Set Complex Filter Topology Asymptotics

set_option linter.unusedSectionVars false

theorem _root_.SWPort.Davenport.logDeriv_LFunction_partial_fraction :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
        ∃ Z : Finset ℂ,
          (↑Z = {ρ ∈ Metric.closedBall (2 + t * Complex.I) (3 / 2) |
                  DirichletCharacter.LFunction χ ρ = 0}) ∧
          (∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
              ≤ C * Real.log ((q : ℝ) * (|t| + 2)) ∧
          ∀ s ∈ Metric.closedBall (2 + t * Complex.I) (7 / 5),
            DirichletCharacter.LFunction χ s ≠ 0 →
              ‖logDeriv (DirichletCharacter.LFunction χ) s
                  - ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
                ≤ C * Real.log ((q : ℝ) * (|t| + 2)) := by
  sorry

end SWPort
end
