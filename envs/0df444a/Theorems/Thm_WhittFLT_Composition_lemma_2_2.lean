-- Prove2me | Theorems.Thm_WhittFLT_Composition_lemma_2_2
-- name    : WhittFLT.Composition.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:19.887491+00:00
-- url     : https://prove2.me/theorems/f0411301-ab2c-4532-a99f-5a5a834e3429
-- title:
--   Lemma 2.2 — splitting $J_1$ convergence at a continuity point
-- statement:
--   Let $a<b<c$ and let $x_n,x$ be càdlàg paths on $[a,c]$ into a metric space $S$. If $x$ is continuous at the interior time $b$, then
--
--   $$
--   x_n\longrightarrow x\text{ in }D([a,c],S)
--   \quad\Longleftrightarrow\quad
--   x_n|_{[a,b]}\longrightarrow x|_{[a,b]}
--   \text{ and }
--   x_n|_{[b,c]}\longrightarrow x|_{[b,c]}
--   \text{ in their respective }J_1\text{ spaces}.
--   $$
--
--   The lemma reconciles the local restriction definition of $J_1$ convergence with convergence on a larger compact interval, and allows composition to be studied on selected compact pieces.
--
--   **Formalization Note** The source prints “convergence to restrictions” and “d([a,b])”; the statement reads these as “converge to restrictions” and $D([a,b])$. Càdlàg membership is explicit. Paths are total real-time functions, restricted through the interval parameters of the $J_1$ distance.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Lemma 2.2, p. 71; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Composition

open Set Filter Topology
open scoped ENNReal

/-- Lemma 2.2, p. 71: splitting J₁ convergence at a continuity point of the limit. -/
theorem lemma_2_2 {S : Type*} [MetricSpace S] (a b c : ℝ) (hab : a < b) (hbc : b < c)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (hxs : ∀ n, IsCadlagOn (Icc a c) (xs n))
    (hx : IsCadlagOn (Icc a c) x) (hb : ContinuousAt x b) :
    J1TendstoOn a c xs x ↔ (J1TendstoOn a b xs x ∧ J1TendstoOn b c xs x) := by sorry

end WhittFLT.Composition
