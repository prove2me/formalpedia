-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_modular_hyperbola
-- name    : QuadraticProbe717.Insertion.modular_hyperbola
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:12.457178+00:00
-- url     : https://prove2.me/theorems/caae0465-545f-4bb4-badc-8f3ba377d2fe
-- title:
--   Lemma 6.3 — modular hyperbolas in translated rectangles
-- statement:
--   For every $\eta>0$ there is $C_\eta>0$ such that the following holds uniformly. Let $n$ be prime and $r\ne0$ modulo $n$. Let $0\le U,V<n$ and $1\le X,Y<n$ be integers. Then
--   $$\#\{(i,j):1\le i\le X,\ 1\le j\le Y,\ (U+i)(V+j)\equiv r\pmod n\}\le C_\eta\left(\frac{XY}{n}+n^{1/2+\eta}\right).$$
--   The coefficient is independent of both translations, both side lengths, the prime and the residue. This is the full rectangle estimate used in the next multiplicity statement.
--
--   Differences from the source:
--   - reading: uniform big-O and n^{1/2+o(1)} → for every η>0 there is Cη>0 before all instance quantifiers, bounding the main term plus n^{1/2+η}; reason: constants depend only on η; finite exceptions are absorbed in Cη
--   - encoding: nonnegative integer translations and modular products → natural endpoints and equality in ZMod n; reason: no translated rectangle or nonzero residue is removed
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 6.3, p. 12 (PDF p. 12)

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem modular_hyperbola :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : n.Prime) (r : ZMod n), r ≠ 0 →
      ∀ U V X Y : ℕ, U < n → V < n → 1 ≤ X → X < n → 1 ≤ Y → Y < n →
        (hyperbolaCount n U V X Y r : ℝ) ≤
          C * ((X : ℝ) * Y / n + (n : ℝ) ^ (1 / 2 + η)) := by sorry

end QuadraticProbe717.Insertion
