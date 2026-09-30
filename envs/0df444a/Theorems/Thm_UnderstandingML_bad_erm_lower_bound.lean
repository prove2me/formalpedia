-- Prove2me | Theorems.Thm_UnderstandingML_bad_erm_lower_bound
-- name    : UnderstandingML.bad_erm_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:59:02.982892+00:00
-- url     : https://prove2.me/theorems/4a684f3f-ee37-4a46-9151-c8c9d00f1f54
-- title:
--   Claim 29.9(2): on a finite domain of size d ≥ 2, for ε ∈ (0,1/2) and m ≤ (d−1)/(6ε), A_bad has error ≥ ε with probability ≥ e^{−1}/6 under the distribution of the proof labeled by h_∅
-- statement:
--   **Claim 29.9(2).** There exists a constant $a > 0$ such that for every $0 < \epsilon < a$ there exists a distribution $D$ over $X$ and $h_A \in H$ such that the following holds. The hypothesis returned by $A_{bad}$ upon receiving a sample of size $m \le \frac{|X|-1}{6\epsilon}$, sampled according to $D$ and labeled by $h_A$, will have error $\ge \epsilon$ with probability $\ge e^{-1}/6$.
--
--   Formally, for $|X| = d \ge 2$ (the case the book proves): for every $\epsilon \in (0, 1/2)$, with the distribution $P[x_0] = 1 - 2\epsilon$, $P[x_i] = 2\epsilon/(d-1)$ of the proof and $h_A = h_\emptyset$, every ERM returning $h_{\{x_1, \dots, x_m\}^c}$ on all-$\ast$ samples has error at least $\epsilon$ with probability at least $e^{-1}/6$ whenever $m \le (d-1)/(6\epsilon)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.4 pp. 407-408, Claim 29.9 part 2 with its proof

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Claim 29.9(2)** (p. 407), for a finite domain `|X| = d ≥ 2`. For every `ε ∈ (0, 1/2)`
(the book: `ε < a` for some constant `a > 0`) there exist a distribution `D` over `X` (the one
of the proof: `P[x₀] = 1 − 2ε`, `P[xᵢ] = 2ε/(d − 1)`) and `h_A ∈ H` (namely `h_∅`) such that the
hypothesis returned by `A_bad` upon receiving a sample of size `m ≤ (|X| − 1)/(6ε)`, sampled
according to `D` and labeled by `h_A`, has error `≥ ε` with probability `≥ e^{−1}/6`. -/
theorem bad_erm_lower_bound {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] (hX : 2 ≤ Fintype.card X) (x₀ : X)
    (A : Learner (X × CofinLabel X) (X → CofinLabel X)) (hA : IsBadERM A) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (m : ℕ) (hm : (m : ℝ) ≤ (Fintype.card X - 1) / (6 * ε)) :
    ENNReal.ofReal (Real.exp (-1) / 6) ≤
      iidLaw ((badDist x₀ ε).map (fun x ↦ (x, hSet ⟨∅, Or.inl Set.finite_empty⟩ x))) m
        {S | ENNReal.ofReal ε ≤ badDist x₀ ε {x | A m S x ≠ hSet ⟨∅, Or.inl Set.finite_empty⟩ x}} := by sorry

end UnderstandingML
