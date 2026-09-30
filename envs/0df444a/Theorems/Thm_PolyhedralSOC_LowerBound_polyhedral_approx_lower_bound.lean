-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_polyhedral_approx_lower_bound
-- name    : PolyhedralSOC.LowerBound.polyhedral_approx_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:50:29.336847+00:00
-- url     : https://prove2.me/theorems/467f1995-0e42-4e98-be02-fe69ed54d623
-- title:
--   Proposition 3.1 — a polyhedral $\varepsilon$-approximation of $L^k$ needs $q\ge\Omega(k\ln(1/\varepsilon))$ inequalities ($k\ge2$)
-- statement:
--   There is a positive absolute constant $c$ such that the following holds. Let $k\ge 2$ be an integer, $\varepsilon\in(0,\tfrac12]$, and let
--   $$\Pi(y,t,u):\mathbb R^k\times\mathbb R\times\mathbb R^p\to\mathbb R^q$$
--   be a polyhedral $\varepsilon$-approximation of the Lorentz cone $L^k=\{(y,t)\mid t\ge\|y\|_2\}$. Then the number of linear inequalities satisfies
--   $$q\ \ge\ c\,k\ln\frac1\varepsilon .$$
--
--   Together with Theorem 1.1 of the same paper, which constructs polyhedral $\varepsilon$-approximations with $p+q\le O(1)\,k\ln(2/\varepsilon)$, this shows that the order $k\ln(1/\varepsilon)$ of the number of inequalities cannot be improved.
--
--   **Formalization Note** The paper's "$q\ge O(1)k\ln\frac1\varepsilon$ with positive absolute constant $O(1)$" is stated as $\exists c>0$ quantified before $k$, $\varepsilon$, $p$, $q$ and $\Pi$. The paper states the proposition for every positive integer $k$; for $k=1$ it is false, since $L^1=\{(y,t)\mid |y|\le t\}$ is polyhedral and $\Pi(y,t)=(t-y,\,t+y)$ ($p=0$, $q=2$) is a polyhedral $\varepsilon$-approximation for every $\varepsilon>0$. The statement is therefore made for $k\ge 2$. The bound concerns $q$ alone.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, Eq. (13); corrected to k ≥ 2

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, Eq. (13), p. 202 (PDF p. 10):
there is a positive absolute constant `c` such that, for every `k ≥ 2`, every `ε ∈ (0, 0.5]` and
every polyhedral `ε`-approximation `Π(y, t, u) : ℝ^k × ℝ × ℝ^p → ℝ^q` of the Lorentz cone `L^k`,
`q ≥ c k ln(1/ε)`.
**Correction:** the paper states this for every positive integer `k`; for `k = 1` it is false,
because `L^1 = {(y, t) | |y| ≤ t}` is polyhedral and `Π(y, t) = (t − y, t + y)` (`p = 0`, `q = 2`)
is a polyhedral `ε`-approximation for every `ε > 0`. The result is stated for `k ≥ 2`. -/
theorem polyhedral_approx_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (p q : ℕ) (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
        Shared.IsPolyhedralApprox k p q ε P → c * k * Real.log (1 / ε) ≤ q := by sorry

end PolyhedralSOC.LowerBound
