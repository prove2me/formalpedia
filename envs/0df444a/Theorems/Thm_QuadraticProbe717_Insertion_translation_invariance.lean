-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_translation_invariance
-- name    : QuadraticProbe717.Insertion.translation_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:50.057587+00:00
-- url     : https://prove2.me/theorems/903f1380-471a-43fc-98f2-ea160d304667
-- title:
--   Observation 3.3 — translation invariance
-- statement:
--   In the algorithm-generated Poissonized table of size $n>0$, let $F_i$ be the vacancy coordinates. For every residue $c$,
--   $$\mathcal L((F_{i+c})_{i\in[n]})=\mathcal L((F_i)_{i\in[n]}).$$
--   The equality is an equality of joint laws, with indices reduced modulo $n$. It is a theorem about the operational construction.
--
--   Differences from the source:
--   - encoding: distinct keys with independent uniform hashes and arbitrary fixed offset completion → insertion-time indices, ZMod n slots, every fixed completion permutation, and exact finite averages; reason: key labels do not affect insertion; repeated quadratic probes and the first empty slot are retained
--   - generalization: Poisson mean (1−ε)n with 0<ε<1 → every nonnegative Poisson mean; reason: translation symmetry does not depend on the mean and specializes to the source regime
--   - encoding: same distribution of vacancy vectors → equality of the two pushforward measures; reason: all maps have finite discrete domain and are measurable
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Observation 3.3, p. 6 (PDF p. 6)

import Definitions.Def_QuadraticProbe717_Insertion_laws

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem translation_invariance (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (rate : ℝ≥0) (c : ZMod n) :
    Measure.map (fun A => fun i : ZMod n => vacancy n (i + c) A) (poissonState n π rate) =
      Measure.map (fun A => fun i : ZMod n => vacancy n i A) (poissonState n π rate) := by sorry

end QuadraticProbe717.Insertion
