-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_growing_teleportation
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.growing_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:52:30.332995+00:00
-- url     : https://prove2.me/theorems/d50cab03-6102-4d75-aaf2-130568b6fd70
-- title:
--   Proposition 3: deterministic MPBT with growing k
-- statement:
--   Fix an integer $d\ge1$, and use the fixed maximally entangled resource with completed SRM. For an integer schedule $k(N)$ satisfying $1\le k(N)\le N$ eventually,
--
--   $$\frac{k(N)}N\longrightarrow0\quad\Longrightarrow\quad F_d(N,k(N))\longrightarrow1.$$
--
--   For every $0<a<1$, the limit $L=\lim_{N\to\infty}F_d(N,\lfloor aN\rfloor)$ exists and obeys
--
--   $$L\ge\exp\!\left(-\frac{(d^2-1)a}{1-a}\right).$$
--
--   The source's assertion of existence of the linear-regime limit is retained as a conclusion. Its proof description misidentifies the bound giving this exponential; the weaker power bound is the relevant expression. Independent moderation should examine this extension beyond the printed range of Theorem 2.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 5, Proposition 3: deterministic MPBT with growing k

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.5, Proposition 3: sublinear fidelity and existence of the linear-regime limit.
The proof uses the weaker power bound; no a<1/2 restriction is introduced. -/
theorem growing_teleportation (d : ℕ) (hd : 1 ≤ d) :
    (∀ k : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) →
      Tendsto (fun N => (k N : ℝ) / (N : ℝ)) atTop (nhds 0) →
      Tendsto (fun N => mpbtFidelity d N (k N)) atTop (nhds 1)) ∧
    (∀ a : ℝ, 0 < a → a < 1 → ∃ L : ℝ,
      Tendsto (fun N : ℕ => mpbtFidelity d N ⌊a * N⌋₊) atTop (nhds L) ∧
      Real.exp (-((d : ℝ)^2 - 1) * a / (1 - a)) ≤ L) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
