-- Prove2me | Theorems.Thm_TopDownParity1043_Main_lemma_12
-- name    : TopDownParity1043.Main.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:20:13.016168+00:00
-- url     : https://prove2.me/theorems/8c16dd53-4add-4833-9451-83e0a5d78fe4
-- title:
--   Lemma 12 — square-root harmonic coefficient inequality
-- statement:
--   For every finite coordinate set $V$ and every $f:\{0,1\}^V\to\mathbb R_{\ge0}$,
--   $$\mathbb E_{R\subseteq_{1/4}V}\sqrt{H_f(R)}\ge\mathbb E_{x\sim\{0,1\}^V}\sqrt{f(x)}.$$
--
--   The left expectation uses independent inclusion with bias exactly $1/4$; the right expectation is uniform on the cube. The result also holds when $V$ is empty or $f$ vanishes, without a normalization assumption. This is the analytic inequality used to control small harmonic coefficients.
--
--   Differences from the source:
--   - encoding: coordinates [n] → an arbitrary finite type V with Boolean words V → Bool; reason: every finite coordinate set is equivalent to Fin |V|, including every subcube coordinate subtype
--   - encoding: finite nonnegative harmonic coefficients and their square roots → values in ℝ≥0∞ and the real power 1/2; reason: these coefficients are always finite, and extended inverses implement exactly the printed conventions at zero
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Lemma 12, p. 17

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
import Definitions.Def_TopDownParity1043_Main_HarmonicMean

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Lemma 12, p.17. Both sides are finite, represented in ENNReal; the real
power 1/2 is the nonnegative square root, including at zero. -/
theorem lemma_12 (V : Type) [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) :
    (cubeMean (fun x => (f x) ^ (1 / 2 : ℝ)) : ℝ≥0∞) ≤
      setMean quarterBias (fun R => (harmonicMean f R) ^ (1 / 2 : ℝ)) := by sorry

end TopDownParity1043.Main
