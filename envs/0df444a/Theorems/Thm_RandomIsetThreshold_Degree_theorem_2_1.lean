-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_theorem_2_1
-- name    : RandomIsetThreshold.Degree.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:13:52.155711+00:00
-- url     : https://prove2.me/theorems/ea9b32da-1837-4251-a750-cb156eae7151
-- title:
--   Theorem 2.1 — exact selector and its low-degree projection
-- statement:
--   Let $2\le r\le k\le n$ be integers and $0<p<1$. Let $h(G)$ be the indicator of the lexicographically first independent $k$-set, or the empty set if none exists. Then
--
--   $$\mathcal I(h)\le2pk\binom{k}{r},\qquad\Pr(h(H_{n,p})\text{ equals an independent }k\text{-set})=\Pr(\alpha(H_{n,p})\ge k).$$
--
--   For every integer $D\ge0$ and $\gamma>0$, the same $h$ has Fourier projection $f=h_{\le D}$ satisfying
--
--   $$\deg(f)\le D,\quad\mathbb E\|f(H_{n,p})\|_2^2\le k,$$
--   $$\Pr\bigl(\exists I\text{ independent}:\ |I|=k,\ \|f(H_{n,p})-1_I\|_2^2\le\gamma k\bigr)\ge\Pr(\alpha(H_{n,p})\ge k)-\frac{\mathcal I(h)}{\gamma k(D+1)}.$$
--
--   This is a finite-sample theorem for every interior bias, with both clauses sharing the actual selector. **Formalization Note** The influence is converted to a real number only here; the first clause bounds it by a finite value, and the deterministic domain is finite.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - generalization: existence of h and its Fourier projection f → the actual lexicographic selector h and its computed projection f; reason: equations (14) and (17) identify these witnesses in the paper proof, yielding the source existentials without extra assumptions
--   - encoding: finite real norms and influence of deterministic functions → extended moments, with influence converted toReal in the error term; reason: the input cube is finite and the first clause supplies finiteness, so no infinite value is collapsed
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 7, Theorem 2.1, equations (11)–(12), witnesses (14), (17) on pp. 7–8

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_SelectorFourier

open MeasureTheory
open scoped ENNReal BigOperators
universe u_theorem_2_1

namespace RandomIsetThreshold.Degree

theorem theorem_2_1
(n r k : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1) :
    let h := selector (r := r) k
    detInfluence p h ≤ ENNReal.ofReal (2 * (p : ℝ) * k * Nat.choose k r) ∧
    (graphLaw n r p).real {G | ∃ I : Finset (Fin n),
      Independent G I ∧ I.card = k ∧ h G = indicator I} =
      (graphLaw n r p).real {G | k ≤ independenceNumber G} ∧
    ∀ (D : ℕ) (γ : ℝ), 0 < γ →
      let f := fourierProjection p D h
      DegreeLE f (D : ℝ) ∧ detNormMoment p f ≤ (k : ℝ≥0∞) ∧
      (graphLaw n r p).real {G | ExactSize k γ G (f G)} ≥
        (graphLaw n r p).real {G | k ≤ independenceNumber G} -
          (detInfluence p h).toReal / (γ * k * ((D : ℝ) + 1)) := by sorry

end RandomIsetThreshold.Degree
