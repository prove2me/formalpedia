-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_shift_intersection
-- name    : QuadraticProbe717.Insertion.shift_intersection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:03.972546+00:00
-- url     : https://prove2.me/theorems/b5b4d83e-061e-4153-b6e6-6adfc6d9f1be
-- title:
--   Lemma 6.5 — intersections of translated square prefixes
-- statement:
--   There exist absolute constants $C,D>0$ with the following property. Let $n_t\to\infty$ be any family of odd primes, let $1\le k_t\le n_t/2$, put $Q_t=\{i^2:0\le i<k_t\}\pmod{n_t}$, and let $J_t$ be any finite sets of distinct shifts such that $|J_t|=o(\log n_t/\log\log n_t)$. Eventually,
--   $$\left|\#\bigcap_{j\in J_t}(Q_t+j)-\frac{k_t^{|J_t|}}{n_t^{|J_t|-1}}\right|\le C\sqrt{n_t}\exp\bigl(D|J_t|\log\log n_t\bigr).$$
--   Both constants precede the choice of every family, and are independent of the shifts and prefix lengths. Empty $J_t$ gives the entire $n_t$-slot universe and main term $n_t$; singleton $J_t$ gives exactly $k_t$.
--
--   **Formalization Note** The denominator uses an integer exponent, including exponent $-1$ for an empty shift set. The dependence on $|J_t|$ is retained, rather than hidden in an $n^{1/2+\eta}$ error. Footnote 5 supplies the underlying error with $r=|J|-1$, degree $d=1$.
--
--   Differences from the source:
--   - reading: |J|=o(log n/log log n) and error O(√n exp(O(|J|log log n))) → absolute C,D outside all families, a little-o hypothesis along any prime-size family, and an eventual bound; reason: a small-o condition is a condition on families; the eventual cutoff may depend on the family, but neither error constant may
--   - encoding: k^{|J|}/n^{|J|−1}, including empty J → integer exponent (|J|:ℤ)−1 in the denominator and empty intersection equal to the universe; reason: preserves the source empty and singleton cases without truncated subtraction
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 6.5 and footnote 5, p. 13 (PDF p. 13)

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem shift_intersection :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (ns ks : ℕ → ℕ) [∀ t, NeZero (ns t)]
        (Js : (t : ℕ) → Finset (ZMod (ns t))),
        Tendsto ns atTop atTop →
        (∀ t, (ns t).Prime ∧ Odd (ns t) ∧ 1 ≤ ks t ∧ 2 * ks t ≤ ns t) →
        Asymptotics.IsLittleO atTop (fun t => ((Js t).card : ℝ))
          (fun t => Real.log (ns t) / Real.log (Real.log (ns t))) →
        ∀ᶠ t in atTop,
          |(shiftIntersection (ns t) (ks t) (Js t)).card -
            (ks t : ℝ) ^ (Js t).card / (ns t : ℝ) ^ ((Js t).card - (1 : ℤ))| ≤
            C * Real.sqrt (ns t) * Real.exp (D * (Js t).card * Real.log (Real.log (ns t))) := by sorry

end QuadraticProbe717.Insertion
