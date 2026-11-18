-- Prove2me | Theorems.Thm_TopDownParity1043_Main_random_set_restriction
-- name    : TopDownParity1043.Main.random_set_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:09:02.902237+00:00
-- url     : https://prove2.me/theorems/11e1ed7e-8e0b-465e-9dbb-62349fc5bc96
-- title:
--   Restriction of a Bernoulli coordinate set to a fixed set
-- statement:
--   Let V be a finite coordinate set, S a fixed subset, p a probability in [0,1], and f a real-valued function on subsets of V. If T includes each coordinate independently with probability p, then
--
--   $$\mathbb E[f(T\cap S)]=\mathbb E[f(R)],$$
--
--   where R is sampled by including each coordinate of S independently with probability p and is then viewed as a subset of V. This identity allows random-set estimates on a coordinate fibre to be applied in the ambient cube.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission 1043, canonical manuscript https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf, p.9 conditional-law discussion and p.12 proof of Lemma 9 (restriction to the coordinate set S).

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
open TopDownParity1043.Main

theorem TopDownParity1043.Main.random_set_restriction (V : Type) [Fintype V] [DecidableEq V] (p : Bias) (S : Finset V) (f : Finset V → ℝ) : (∑ T : Finset V, setWeight p T * f (T ∩ S)) = ∑ R : Finset S, setWeight p R * f (R.map (Function.Embedding.subtype _)) := by sorry
