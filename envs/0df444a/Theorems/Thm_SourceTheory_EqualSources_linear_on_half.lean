-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_linear_on_half
-- name    : SourceTheory.EqualSources.linear_on_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:05.23522+00:00
-- url     : https://prove2.me/theorems/aa371415-de4e-4dd0-9d5d-ede6a72c346f
-- title:
--   Proof of Theorem 4, p. 8780 (Online App. A) — if φ and φ⁻¹ are both sub-additive on [0, 1/2] and φ(1/2) = 1/2, φ is linear on [0, 1/2]
-- statement:
--   Let $\varphi$ be a transformation: continuous and strictly increasing on $[0,1]$, mapping $[0,1]$ into $[0,1]$, with $\varphi(0) = 0$ and $\varphi(1) = 1$. Let $\psi$ be its inverse on $[0,1]$ ($\psi(\varphi(p)) = p$ and $\varphi(\psi(p)) = p$ for $p \in [0,1]$), and suppose $\varphi(\tfrac12) = \tfrac12$. If for all $p, \varepsilon \ge 0$ with $p + \varepsilon \le \tfrac12$
--
--   $$\varphi(p+\varepsilon) - \varphi(p) \le \varphi(\varepsilon) \quad\text{and}\quad \psi(p+\varepsilon) - \psi(p) \le \psi(\varepsilon),$$
--
--   then $\varphi$ is linear on $[0, \tfrac12]$: there is a constant $c$ with $\varphi(p) = c\,p$ for all $p \in [0, \tfrac12]$.
--
--   This is the functional-equation step of the proof of Theorem 4; the paper defers its proof to its Online Appendix A.
--
--   **Formalization Note.** The hypothesis $\varphi(\tfrac12) = \tfrac12$ is the context the proof of Theorem 4 has established at this point ("Hence, $\varphi(\tfrac12) = \tfrac12$"). Without it the two inequalities give additivity only where $\varphi(p) + \varphi(\varepsilon) \le \tfrac12$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 4, p. 8780 (proof deferred to Online Appendix A)

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Proof of Theorem 4, p. 8780 (proof in the Online Appendix A): a continuous, strictly increasing
`φ` on `[0, 1]` with `φ(0) = 0`, `φ(1) = 1`, `φ(1/2) = 1/2` such that both `φ` and its inverse `ψ`
are sub-additive on `[0, 1/2]` is linear on `[0, 1/2]`. -/
theorem linear_on_half (φ ψ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ)
    (hψ : ∀ p ∈ Icc (0 : ℝ) 1, ψ (φ p) = p ∧ φ (ψ p) = p) (hhalf : φ (1 / 2) = 1 / 2)
    (hsub : ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → φ (p + ε) - φ p ≤ φ ε)
    (hsubψ : ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → ψ (p + ε) - ψ p ≤ ψ ε) :
    ∃ c : ℝ, ∀ p ∈ Icc (0 : ℝ) (1 / 2), φ p = c * p := by sorry

end SourceTheory.EqualSources
