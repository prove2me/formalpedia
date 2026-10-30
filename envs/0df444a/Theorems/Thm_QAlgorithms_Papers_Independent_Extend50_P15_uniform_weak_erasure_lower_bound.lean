-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_uniform_weak_erasure_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.uniform_weak_erasure_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:56:13.484142+00:00
-- url     : https://prove2.me/theorems/e3da4981-7fe2-447a-a16a-a9e4fdc60f27
-- title:
--   Uniform fixed-size erasure lower bound for all covariant codes
-- statement:
--   Let $d\ge2$ and $1\le n_e\le n$. Consider any CPTP encoder from one logical $d$-level system to $n$ physical $d$-level systems that exactly intertwines all defining $\mathrm{SU}(d)$ gates with a fixed transversal product of that gate or identity on each site. Let the decoder be any CPTP recovery from the full flagged output space. Erase a uniformly selected subset of exactly $n_e$ sites: each such subset has probability $\binom n{n_e}^{-1}$ and all other subsets have probability zero. Then
--
--   $$\epsilon_{\mathrm{cov}}\ge\frac{1}{16n^2(1+1/n_e)}.$$
--
--   Here $\epsilon_{\mathrm{cov}}$ is the maximum over logical gates of half the diamond distance between the implemented and ideal logical channel. The result constrains every such covariant code, independently of any reference-frame ansatz.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 23, Proposition 1, B19--B20

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 1, B20, PDF pp.5,23. All covariant codes are covered, independently
of Protocol 1; the subset law, p0=0, and 1≤ne≤n are explicit. -/
theorem uniform_weak_erasure_lower_bound (d n ne : ℕ) (hd : 2 ≤ d)
    (hne : 1 ≤ ne) (hnen : ne ≤ n) (code : CovariantCode d n) :
    1 / (16 * (n : ℝ) ^ 2 * (1 + 1 / (ne : ℝ))) ≤
      covariantError code (uniformSubsetErasure d n ne) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
