-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_lorentz_cone_polyhedral_approximation
-- name    : PolyhedralSOC.UpperBound.lorentz_cone_polyhedral_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:50:38.953599+00:00
-- url     : https://prove2.me/theorems/96b11d0c-e777-4a5d-8889-180e01006950
-- title:
--   Theorem 1.1 — $L^k$ has a polyhedral $\varepsilon$-approximation with $p_k+q_k\le O(1)\,k\ln(2/\varepsilon)$
-- statement:
--   There is an absolute constant $C>0$ such that for every positive integer $k$ and every $\varepsilon\in(0,1]$ the Lorentz cone
--   $$L^k=\{(y,t)\in\mathbb R^k\times\mathbb R\mid t\ge\|y\|_2\}$$
--   admits a polyhedral $\varepsilon$-approximation, i.e. a linear map $\Pi:\mathbb R^k\times\mathbb R\times\mathbb R^{p_k}\to\mathbb R^{q_k}$ such that (i) every $(y,t)\in L^k$ has some $u$ with $\Pi(y,t,u)\ge0$ and (ii) $\Pi(y,t,u)\ge0$ for some $u$ implies $\|y\|_2\le(1+\varepsilon)t$, whose sizes satisfy
--   $$p_k+q_k\le C\,k\ln\frac{2}{\varepsilon}.\tag{1}$$
--
--   A conic quadratic program can therefore be approximated to relative accuracy $\varepsilon$ by a linear program whose size grows only like $k\ln(1/\varepsilon)$, not exponentially in $k$.
--
--   **Formalization Note** The paper's $O(1)$ is an absolute constant; it is the existential $C$, quantified before $k$ and $\varepsilon$. $\Pi$ must be $\mathbb R$-linear (`→ₗ[ℝ]`), vectors of $\mathbb R^k$ are `Fin k → ℝ`, and $\|\cdot\|_2$ is the Euclidean norm written out as a square root of a sum of squares. $\ln$ is `Real.log`.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 195, Theorem 1.1, Eq. (1)

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Theorem 1.1, p. 195 (PDF p. 3): there is an
absolute constant `C` such that for every positive integer `k` and every `ε ∈ (0, 1]`,
the Lorentz cone `L^k` admits a polyhedral `ε`-approximation (a linear map
`Π : ℝ^k × ℝ × ℝ^p → ℝ^q`) with `p + q ≤ C · k · ln(2/ε)` (Eq. (1)). -/
theorem lorentz_cone_polyhedral_approximation :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (p q : ℕ) (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
        Shared.IsPolyhedralApprox k p q ε P ∧ ((p + q : ℕ) : ℝ) ≤ C * k * Real.log (2 / ε) := by sorry

end PolyhedralSOC.UpperBound
