-- Prove2me | Theorems.Thm_WassDRCCP_Improved_eq_6_bigM_reformulation
-- name    : WassDRCCP.Improved.eq_6_bigM_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:20.652441+00:00
-- url     : https://prove2.me/theorems/b208b2b0-1fad-4812-b884-6e875e88c1c0
-- title:
--   (6), p. 646 (Chen–Kuhn–Wiesemann, Prop 2) — big-M MIP (5) is exact: X_DR(S) = {x ∈ X : (5b)–(5e)}
-- statement:
--   Consider the safety set $\mathcal S(x) = \{\xi : b_p^\top\xi + d_p - a_p^\top x > 0,\ p \in [P]\}$ of a joint chance constraint with right-hand side uncertainty, in a finite-dimensional real normed space $E$, with $P \ge 1$ and every $b_p \ne 0$. Let $\xi_1, \dots, \xi_N$ be a sample ($N \ge 1$), $\epsilon \in (0,1)$, $\theta > 0$, $\mathcal X \subseteq \mathbb R^L$, and let $M$ be a constant with
--   $$\frac{|b_p^\top\xi_i + d_p - a_p^\top x|}{\|b_p\|_*} \le M \quad\text{for all } x \in \mathcal X,\ i \in [N],\ p \in [P].$$
--   Then
--   $$\mathcal X_{\mathrm{DR}}(\mathcal S) = \{x \in \mathcal X : \exists\, (z, r, t) \text{ satisfying (5b)–(5e)}\},$$
--   where (5b) is $z \in \{0,1\}^N$, $t \ge 0$, $r \ge 0$, $x \in \mathcal X$; (5c) is $\epsilon t \ge \theta + \frac1N\sum_i r_i$; (5d) is $M(1 - z_i) \ge t - r_i$ for $i \in [N]$; and (5e) is $\frac{b_p^\top\xi_i + d_p - a_p^\top x}{\|b_p\|_*} + M z_i \ge t - r_i$ for $i \in [N]$, $p \in [P]$.
--
--   This is the big-M mixed-integer reformulation of Chen, Kuhn and Wiesemann (Proposition 2), the baseline formulation that the paper strengthens.
--
--   **Formalization Note** The paper's "$M$ is a sufficiently large positive constant" is pinned by Remark 1, (10): $M := \max_{x\in\mathcal X, p\in[P]} |b_p^\top\xi_i + d_p - a_p^\top x|/\|b_p\|_*$, taken here as a single bound uniform over $i$ (one $M$ appears in (5)). Instead of assuming $\mathcal X$ compact (p. 642), the existence of this bound is assumed. $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$ are the standing assumptions of §§2–4; $P \ge 1$ and $b_p \ne 0$ make (4) well defined. The binaries are real numbers with $z_i \in \{0, 1\}$.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 646, (5)–(6), citing Chen, Kuhn & Wiesemann [8, Proposition 2]; M as in Remark 1, (10), pp. 648–649

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), (6), p. 646 (Chen, Kuhn & Wiesemann,
Proposition 2): for the safety set (4a), `X_DR(S) = {x ∈ X : (5b)–(5e)}`, with the big-M
constant `M` bounding every `|b_p^⊤ξ_i + d_p − a_p^⊤x|/‖b_p‖_*` over `x ∈ X` (Remark 1, (10)). -/
theorem eq_6_bigM_reformulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hM : ∀ x ∈ X, ∀ (i : Fin N) (p : Fin P), |b p (ξ i) + d p - a p ⬝ᵥ x| / ‖b p‖ ≤ M) :
    XDR (safetySet a b d) X ξ ϵ θ =
      {x | x ∈ X ∧ ∃ (z r : Fin N → ℝ) (t : ℝ), sys5 a b d ξ X ϵ θ M x z r t} := by sorry

end WassDRCCP.Improved
