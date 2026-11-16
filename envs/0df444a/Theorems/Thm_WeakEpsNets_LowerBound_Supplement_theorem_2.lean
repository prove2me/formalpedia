-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_Supplement_theorem_2
-- name    : WeakEpsNets.LowerBound.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:34.70755+00:00
-- url     : https://prove2.me/theorems/cb522dec-634f-4afc-864c-5e5d6b949e17
-- title:
--   Theorem 2 — weak nets in $\mathbb R^4$ need $q^3/2+q^2$ points, and $f_4(r)=\Omega(r^{3/2})$
-- statement:
--   A **weak $1/r$-net** of a finite nonempty point set $P\subset\mathbb R^d$ is a finite set $X\subset\mathbb R^d$ that meets every convex set $C$ with $|C\cap P|\ge |P|/r$; the points of $X$ may lie anywhere in $\mathbb R^d$. Write $f_d(r)$ for the largest, over finite nonempty $P\subset\mathbb R^d$, of the minimum size of a weak $1/r$-net of $P$ (a value in $\mathbb N\cup\{\infty\}$).
--
--   The theorem has two parts.
--
--   1. For every even integer $q\ge2$ there is a set $P\subset\mathbb R^4$ with exactly $|P|=2q^3$ points such that every weak $\frac{1}{4q^2}$-net $X$ of $P$ satisfies
--   $$|X|\ \ge\ \frac{q^3}{2}+q^2 .$$
--   2. Consequently $f_4(r)=\Omega(r^{3/2})$: there are constants $r_0>0$ and $c>0$ such that
--   $$f_4(r)\ \ge\ c\,r^{3/2}\qquad\text{for every real } r\ge r_0 .$$
--
--   In the source the witness is the grid $[q]\times[2q^2]$ lifted to $\mathbb R^4$ by $\psi(x,y)=(x,y,x^2,xy)$; the statement is existential in $P$ and does not fix the witness. This is the paper's four-dimensional warm-up. Its exponent $3/2$ agrees with the mission goal at $d=4$, while the first part gives, for each $q$, an explicit bound that the goal does not state.
--
--   **Formalization Note** $\mathbb R^4$ is `Fin 4 → ℝ`, point sets and nets are `Finset`s, and the net threshold $|P|/r$ uses real division (the published `IsWeakNet`). The constants $q^3/2$ and $q^2$ are computed in $\mathbb R$. $f_4$ takes values in $\mathbb N\cup\{\infty\}$ and is compared in $[0,\infty]$, so an infinite value is not truncated; this is the same reading of $\Omega$ as in the published goal `theorem_1`.
--
--   Differences from the source:
--   - encoding: $f_4(r)=\Omega(r^{3/2})$ → there exist $r_0>0$, $c>0$ with ENNReal.ofReal(c·r^{3/2}) ≤ f 4 r for all real r ≥ r_0; reason: the standard meaning of Ω as r → ∞, identical to the published goal's reading
--   - encoding: $\mathbb R^4$, point sets, weak nets → Fin 4 → ℝ, Finset, the published IsWeakNet with real threshold |P|/r; reason: Lean conventions; the same instances
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Theorem 2, p. 7, lines 216–217 (proof §2.1, pp. 6–7, lines 177–215); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Nets
import Definitions.Def_WeakEpsNets_LowerBound_Extremal

open scoped ENNReal

namespace WeakEpsNets.LowerBound.Supplement

/-- Theorem 2, source p. 7 (§2.1, proof pp. 6–7), both clauses.
(i) For every even integer q ≥ 2 some 2q³-point set P ⊂ ℝ⁴ has every finite weak
1/(4q²)-net of size at least q³/2 + q² (real arithmetic).
(ii) f₄(r) = Ω(r^{3/2}), read as in the published goal: positive constants r₀, c with
c · r^{3/2} ≤ f₄(r) in ℝ≥0∞ for every real r ≥ r₀. -/
theorem theorem_2 :
    (∀ q : ℕ, 2 ≤ q → Even q →
      ∃ P : Finset (Fin 4 → ℝ), P.card = 2 * q ^ 3 ∧
        ∀ X : Finset (Fin 4 → ℝ), IsWeakNet P (4 * (q : ℝ) ^ 2) X →
          (q : ℝ) ^ 3 / 2 + (q : ℝ) ^ 2 ≤ (X.card : ℝ)) ∧
    (∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ r : ℝ, r₀ ≤ r →
        ENNReal.ofReal (c * Real.rpow r (3 / 2 : ℝ)) ≤ (f 4 r : ℝ≥0∞)) := by sorry

end WeakEpsNets.LowerBound.Supplement
