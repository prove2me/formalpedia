-- Prove2me | Theorems.Thm_WeldedPath_Supplement_localized_oracle_comparison
-- name    : WeldedPath.Supplement.localized_oracle_comparison
-- status  : Open
-- author  : @dmilosch
-- created : 2026-11-22T16:09:29.552801+00:00
-- url     : https://prove2.me/theorems/9f73a886-cfb6-4340-a59d-2132a742fd74
-- title:
--   Localized exact-versus-ordinary query correction
-- statement:
--   Let $P_t=\Pi_t^{\mathrm{good}}(V_{\mathrm{bd}})$, $N=2^n$, and $t\le6q$. For a valid welded-tree instance with even $n\ge16$ and $2\le\ell\le n-4$, there are absolute $C_0,C>0$ such that the two conditions of Eq. (49) imply
--   $$
--   \left\|(I-P_{t+6})(\widehat{\mathrm{cpWT}}-\mathrm{cpWT})P_t\right\|
--   \le C\sqrt{\frac{n(t+1)}{2^n}}.
--   $$
--   This isolates the exact-minus-ordinary correction in the proof of Proposition 4.12. It is a leakage bound, not an unprojected norm comparison. Ordinary goodness (Theorem 4.9) is a separate input to the parent result.
--
--   Proof route: truncate each class correction at $t+6$ records. For small classes enlarge the boundary by both endpoint sets; Lemmas 4.10 and 4.11 give a nearby commuting good projector. For large classes use the zero projector. The class norm times the projector change is $O(\sqrt{(t+6)/N})$ in both cases. Orthogonal class supports give a total commutator $O(\sqrt{n(t+6)/N})$. Equation (43) and inverse-label goodness add $O(N^{-1}+\sqrt{(t+1)/M})$, absorbed into the displayed bound.
--
--   Formalization note: this is the comparison term extracted from Proposition 4.12, not a separately numbered statement. Constants precede every instance and query parameter; the stated bound includes $t=0$.
-- source:
--   Carolan et al., Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912v1, Section 4.3, comparison term in the proof of Proposition 4.12; Eq. (43), Lemmas 4.7, 4.10, 4.11 and 2.3. https://arxiv.org/html/2611.05912v1#S4.SS3

import Definitions.Def_WeldedPath_Supplement_projGood
import Definitions.Def_WeldedPath_Supplement_exactCpWT

namespace WeldedPath.Supplement

/-- The projected exact-minus-ordinary correction, localized by enlarging each
small edge class's boundary. This is the comparison part of Proposition 4.12,
using (43), Lemmas 4.7, 4.10, 4.11 and the orthogonal class commutator bound. -/
theorem localized_oracle_comparison :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q →
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      ‖(1 - projGood l G (t + 6)).comp
        (((exactCpWT l G) - cpWT l G).comp (projGood l G t))‖ ≤
          C * Real.sqrt ((n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n) := by sorry

end WeldedPath.Supplement
