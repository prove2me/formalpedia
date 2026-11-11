-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_5
-- name    : RandKSATSample.Main.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:01.799089+00:00
-- url     : https://prove2.me/theorems/3aaba818-c1f1-414e-b1b2-3fb1f11f17a5
-- title:
--   Lemma 3.5 — on the joint event, unions U of core components have |U| ≤ (k/2)|U ∩ V_high|, and each component has at most log₂ n variables
-- statement:
--   Let $k\ge30$ and assume the joint event of Lemmas 3.1 to 3.3 (expansion, incidence, $|V_{\mathrm{high}}|\le r$). Let $B_1,\dots,B_s$ be the connected components of $G_\Phi[V_{\mathrm{bad}}]$, $V_{\mathrm{bad}}=\mathrm{Core}(V_{\mathrm{high}})$. For every nonempty $J\subseteq[s]$ and $U=\bigcup_{i\in J}B_i$,
--   $$|U|\le\frac k2\,|U\cap V_{\mathrm{high}}|,$$
--   and every component satisfies $|B_i|\le\log_2 n$. Small components let the sampler enumerate and resample each component of the core.
--
--   Differences from the source:
--   - reading: Assume the joint event of Lemmas 3.1 to 3.3 → hypotheses JointEvent Φ and k ≥ 30; reason: the joint event is that of Lemmas 3.1 and 3.3, which are stated for k ≥ 30, and the proof uses k ≥ 30 (p. 15, last display); without it the statement fails (k = 1, see INSIGHTS.yaml I1)
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 15, Lemma 3.5

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

namespace RandKSATSample.Main

/-- Lemma 3.5: on the joint event of Lemmas 3.1–3.3 (whose lemmas assume `k ≥ 30`), every union
`U` of a nonempty set of core components satisfies `|U| ≤ (k/2)|U ∩ V_high|`, and every
component has at most `log₂ n` variables. -/
theorem lemma_3_5 {n m k : ℕ} (hk : 30 ≤ k) (Φ : Formula n m k) (hJ : JointEvent Φ) :
    (∀ Jb ⊆ blocks Φ, Jb.Nonempty →
      ((Jb.biUnion id).card : ℝ) ≤ (k : ℝ) / 2 * ((Jb.biUnion id ∩ Vhigh Φ).card : ℝ)) ∧
    ∀ Bi ∈ blocks Φ, (Bi.card : ℝ) ≤ Real.logb 2 n := by sorry

end RandKSATSample.Main
