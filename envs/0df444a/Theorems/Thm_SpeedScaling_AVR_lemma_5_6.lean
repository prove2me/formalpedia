-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_6
-- name    : SpeedScaling.AVR.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:22.909904+00:00
-- url     : https://prove2.me/theorems/4ceefbd5-2a17-4f9d-b94d-63c0eac48546
-- title:
--   Lemma 5.6 — reduction to canonical instances
-- statement:
--   For any instance optimized by speed $s^*$, there are fixed execution intervals, speeds, and job types that reproduce $s^*$ almost everywhere in the scheduling window and admit at least one canonical consistent instance. Every upper bound $c$ on $F_A+F_B$ for canonical instances with those fixed data gives
--   $$\operatorname{AVR}(J)\le 2c.$$
--
--   This expresses the paper's supremum bound without taking a real supremum of a possibly empty set.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 380, Lemma 5.6 and Eq. (10).

import Definitions.Def_SpeedScaling_AVR_Consistent

namespace SpeedScaling.AVR
open MeasureTheory

theorem lemma_5_6 {n : ℕ} (J : Instance n) (S : Schedule n)
    (hS : IsOptimal (fun x : ℝ => x ^ 2) J S) :
    ∃ D : ExecData,
      (∀ i : Fin D.m, Set.Icc (D.aS i) (D.bS i) ⊆ Set.Icc J.t0 J.t1) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc J.t0 J.t1)),
        (∑ i : Fin D.m, sStar D i t) = S.s t) ∧
      (∃ x y : Fin D.m → ℝ, CanonicalConsistent D x y) ∧
      (∀ c : ℝ,
        (∀ x y : Fin D.m → ℝ,
          CanonicalConsistent D x y → FA D x + FB D y ≤ c) →
        AVR J ≤ 2 * c) := by sorry

end SpeedScaling.AVR
