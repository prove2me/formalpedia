-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_psi_conditions
-- name    : UncoupledDyn.Continuum.psi_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:26.689973+00:00
-- url     : https://prove2.me/theorems/4599b7d4-7b06-4d9a-915f-9728e457b38c
-- title:
--   Appendix, p. 1835, and fn. 21 — the functions ψ_a satisfy conditions (1)–(4)
-- statement:
--   Let $\varphi$ be the explicit map of §II and, for $\varepsilon>0$ and $\|a\|<\varepsilon$, let $\psi_a$ be the Appendix's function: $\psi_a(z)=a$ for $\|z\|\le2\varepsilon$, $\psi_a(z)=0$ for $\|z\|=3\varepsilon$, $\psi_a(z)$ is $\varphi(z)$ rotated by the angle $\varepsilon$ for $\|z\|\ge4\varepsilon$, and $\psi_a$ is linear on rays in $2\varepsilon<\|z\|<3\varepsilon$ and in $3\varepsilon<\|z\|<4\varepsilon$.
--
--   There are constants $C>0$ and $\varepsilon_0>0$ such that for every $0<\varepsilon<\varepsilon_0$ and all $a,b$ with $\|a\|<\varepsilon$, $\|b\|<\varepsilon$, the function $\psi_a$ is a continuous map $D\to D$ and
--   1. $\|\psi_a(z)-\varphi(z)\|\le C\varepsilon$ for all $z\in D$;
--   2. $\psi_a(z)=a$ for all $\|z\|\le2\varepsilon$;
--   3. for $z\in D$: $\ \varphi(\psi_a(z))=z\iff z=2a$;
--   4. for $z\in D$: $\ \psi_b(\psi_a(z))=z\iff z=b$.
--
--   By (3) and (4) the games built from $(\varphi,\psi_b)$ and $(\psi_a,\psi_b)$ belong to $\mathcal U_0$, by (1) they are close to $\Gamma_0$, and by (2) they replace the constant best replies used in the proof of Lemma 2.
--
--   **Formalization Note.** The page leaves $\varepsilon$ small but unquantified; the statement asks for some threshold $\varepsilon_0$. The constant $C$ is uniform in $\varepsilon$, $a$ and $b$. In (3) the page writes $z=\varphi(a)=2a$ and in (4) $z=\psi_b(a)=b$. $\mathbb R^2$ is $\mathbb C$ and rotation by $\varepsilon$ is multiplication by $e^{i\varepsilon}$.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1835, Appendix, conditions (1)–(4), construction (i)–(iv), fn. 21

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- Appendix, p. 1835, and footnote 21: there are `C > 0` and `ε₀ > 0` such that for every
`0 < ε < ε₀` and all `a, b` with `‖a‖, ‖b‖ < ε`, `ψ_a` is a continuous map `D → D` and
(1) `‖ψ_a − φ‖ ≤ Cε` on `D`; (2) `ψ_a(z) = a` for `‖z‖ ≤ 2ε`; (3) `φ(ψ_a(z)) = z` iff `z = 2a`;
(4) `ψ_b(ψ_a(z)) = z` iff `z = b`. -/
theorem psi_conditions :
    ∃ C > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ a b : ℂ, ‖a‖ < ε → ‖b‖ < ε →
      (ContinuousOn (psi ε a) D ∧ Set.MapsTo (psi ε a) D D) ∧
      (∀ z ∈ D, ‖psi ε a z - phi z‖ ≤ C * ε) ∧
      (∀ z : ℂ, ‖z‖ ≤ 2 * ε → psi ε a z = a) ∧
      (∀ z ∈ D, phi (psi ε a z) = z ↔ z = 2 * a) ∧
      (∀ z ∈ D, psi ε b (psi ε a z) = z ↔ z = b) := by sorry

end UncoupledDyn.Continuum
