-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_covering_count
-- name    : PolyhedralSOC.LowerBound.covering_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:49:54.641361+00:00
-- url     : https://prove2.me/theorems/9cf51ba4-b482-4d9c-8880-0599adaf06e2
-- title:
--   Proposition 3.1, proof — covering $\partial((1+\varepsilon)B)$ needs $\exp\{\Omega(k\ln 1/\varepsilon)\}$ balls ($k\ge2$)
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $k\ge 2$, $0<\varepsilon\le\tfrac12$, and let $S\subseteq\mathbb R^k$ be a finite set such that the closed Euclidean balls of radius $\sqrt{2\varepsilon(1+\varepsilon)}$ centred at the points of $S$ cover the sphere $\{y\mid\|y\|_2=1+\varepsilon\}$. Then
--   $$|S|\ \ge\ \exp\{c\,k\ln(1/\varepsilon)\}.$$
--
--   Combined with the bound $|S|=N\le 2^q$ on the number of vertices of the slice $G$, this gives the lower bound on $q$.
--
--   **Formalization Note** The paper writes $N\ge\exp\{O(1)k\ln 1/\varepsilon\}$ "with a positive absolute constant $O(1)$"; this is stated as $\exists c>0$ quantified before $k$, $\varepsilon$ and $S$. The page does not restrict $k$; for $k=1$ the sphere consists of two points, covered by two balls, so the claim is false for $k=1$ and is stated for $k\ge 2$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, proof ("For ε ≤ 0.5, the fact that the balls B_i cover ∂((1+ε)B) implies that N ≥ exp{O(1)k ln 1/ε}"); corrected to k ≥ 2

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, proof, p. 202 (PDF p. 10):
"For ε ≤ 0.5, the fact that the balls B_i cover ∂((1+ε)B) implies that
N ≥ exp{O(1) k ln 1/ε} with a positive absolute constant O(1)."
There is an absolute constant `c > 0` such that for every `k ≥ 2`, every `ε ∈ (0, 1/2]` and
every finite set `S ⊆ ℝ^k` for which the closed Euclidean balls of radius `√(2ε(1+ε))` centred
at the points of `S` cover the sphere `{‖y‖₂ = 1 + ε}`, one has `|S| ≥ exp(c k ln(1/ε))`.
**Correction:** the page does not restrict `k`; for `k = 1` the sphere is two points, covered by
`N = 2` balls, so the claim is false and is stated for `k ≥ 2`. -/
theorem covering_count :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ S : Finset (Fin k → ℝ),
        (∀ y : Fin k → ℝ, Shared.eucNorm y = 1 + ε →
          ∃ s ∈ S, Shared.eucNorm (y - s) ≤ Real.sqrt (2 * ε * (1 + ε))) →
        Real.exp (c * k * Real.log (1 / ε)) ≤ S.card := by sorry

end PolyhedralSOC.LowerBound
