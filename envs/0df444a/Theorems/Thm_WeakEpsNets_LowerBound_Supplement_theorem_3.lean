-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_Supplement_theorem_3
-- name    : WeakEpsNets.LowerBound.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:33:08.814789+00:00
-- url     : https://prove2.me/theorems/39142b98-8176-447d-812d-ddcacef04a04
-- title:
--   Theorem 3 — weak nets in $\mathbb R^3$ need $q^3/8+q^2/4$ points, and $f_3(r)=\Omega(r^{3/2})$
-- statement:
--   A **weak $1/r$-net** of a finite nonempty point set $P\subset\mathbb R^d$ is a finite set $X\subset\mathbb R^d$ that meets every convex set $C$ with $|C\cap P|\ge |P|/r$; the points of $X$ may lie anywhere in $\mathbb R^d$. Write $f_d(r)$ for the largest, over finite nonempty $P\subset\mathbb R^d$, of the minimum size of a weak $1/r$-net of $P$ (a value in $\mathbb N\cup\{\infty\}$).
--
--   The theorem has two parts.
--
--   1. For every even integer $q\ge2$ there is a set $P\subset\mathbb R^3$ with exactly $|P|=2q^3$ points such that every weak $\frac{1}{4q^2}$-net $X$ of $P$ satisfies
--   $$|X|\ \ge\ \frac{q^3}{8}+\frac{q^2}{4} .$$
--   2. Consequently $f_3(r)=\Omega(r^{3/2})$: there are constants $r_0>0$ and $c>0$ such that
--   $$f_3(r)\ \ge\ c\,r^{3/2}\qquad\text{for every real } r\ge r_0 .$$
--
--   In the source the witness is the grid $\{(a,b+\tau):a\in[q],\ b\in[2q^2]\}$, shifted by $\tau=1/(9q^5)$ and lifted to $\mathbb R^3$ by $\phi(x,y)=(x^2,xy,y^2)$; the statement is existential in $P$ and does not fix the witness. This is the three-dimensional case of the paper's construction. Its exponent $3/2$ agrees with the mission goal at $d=3$, while the first part gives, for each $q$, an explicit bound in $\mathbb R^3$ itself.
--
--   **Formalization Note** $\mathbb R^3$ is `Fin 3 → ℝ`, point sets and nets are `Finset`s, and the net threshold $|P|/r$ uses real division (the published `IsWeakNet`). The constants $q^3/8$ and $q^2/4$ are computed in $\mathbb R$. $f_3$ takes values in $\mathbb N\cup\{\infty\}$ and is compared in $[0,\infty]$, so an infinite value is not truncated; this is the same reading of $\Omega$ as in the published goal `theorem_1`.
--
--   Differences from the source:
--   - encoding: $f_3(r)=\Omega(r^{3/2})$ → there exist $r_0>0$, $c>0$ with ENNReal.ofReal(c·r^{3/2}) ≤ f 3 r for all real r ≥ r_0; reason: the standard meaning of Ω as r → ∞, identical to the published goal's reading
--   - encoding: $\mathbb R^3$, point sets, weak nets → Fin 3 → ℝ, Finset, the published IsWeakNet with real threshold |P|/r; reason: Lean conventions; the same instances
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Theorem 3, p. 8, lines 248–249 (proof §2.2, pp. 7–9, lines 219–246, using Lemma 1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Nets
import Definitions.Def_WeakEpsNets_LowerBound_Extremal

open scoped ENNReal

namespace WeakEpsNets.LowerBound.Supplement

/-- Theorem 3, source p. 8 (§2.2, proof pp. 7–9), both clauses.
(i) For every even integer q ≥ 2 some 2q³-point set P ⊂ ℝ³ has every finite weak
1/(4q²)-net of size at least q³/8 + q²/4 (real arithmetic).
(ii) f₃(r) = Ω(r^{3/2}), read as in the published goal: positive constants r₀, c with
c · r^{3/2} ≤ f₃(r) in ℝ≥0∞ for every real r ≥ r₀. -/
theorem theorem_3 :
    (∀ q : ℕ, 2 ≤ q → Even q →
      ∃ P : Finset (Fin 3 → ℝ), P.card = 2 * q ^ 3 ∧
        ∀ X : Finset (Fin 3 → ℝ), IsWeakNet P (4 * (q : ℝ) ^ 2) X →
          (q : ℝ) ^ 3 / 8 + (q : ℝ) ^ 2 / 4 ≤ (X.card : ℝ)) ∧
    (∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ r : ℝ, r₀ ≤ r →
        ENNReal.ofReal (c * Real.rpow r (3 / 2 : ℝ)) ≤ (f 3 r : ℝ≥0∞)) := by sorry

end WeakEpsNets.LowerBound.Supplement
