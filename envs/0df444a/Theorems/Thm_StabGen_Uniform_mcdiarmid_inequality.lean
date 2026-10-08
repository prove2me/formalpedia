-- Prove2me | Theorems.Thm_StabGen_Uniform_mcdiarmid_inequality
-- name    : StabGen.Uniform.mcdiarmid_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:47:32.44798+00:00
-- url     : https://prove2.me/theorems/e9f8d74d-ea17-45b1-90c9-c625bfe68a21
-- title:
--   McDiarmid's bounded-differences inequality (Theorem 2)
-- statement:
--   Let $Z$ be a measurable space, $D$ a probability measure on $Z$, and $S = (z_1, \dots, z_m)$ a sample drawn from $D^m$. For a sample $S$, an index $i$ and a point $z_i' \in Z$, let $S^i$ be $S$ with $z_i$ replaced by $z_i'$. Let $F : Z^m \to \mathbb R$ be a measurable function with bounded differences: there are constants $c_1, \dots, c_m$ with
--
--   $$\sup_{S \in Z^m,\ z_i' \in Z} |F(S) - F(S^i)| \le c_i \qquad (i = 1, \dots, m).$$
--
--   Then for every $\epsilon > 0$,
--
--   $$P_S\big[F(S) - \mathbb E_S[F(S)] \ge \epsilon\big] \le \exp\Big(-\frac{2\epsilon^2}{\sum_{i=1}^m c_i^2}\Big).$$
--
--   This is the concentration inequality from which the paper derives its exponential bounds: the generalization gap of a uniformly stable algorithm has bounded differences, so it concentrates around its mean.
--
--   **Formalization Note** The paper prints the upper summation index as $n$; this is a slip for $m$, the number of coordinates, and the sum here runs over $i = 1, \dots, m$. The constants $c_i$ may differ from coordinate to coordinate. If every $c_i = 0$, the paper's displayed fraction has zero denominator; the formal statement uses its natural zero tail bound, since bounded differences then force $F$ to be constant. The probability is the product measure `Measure.pi` of the bad set, and the expectation is the Bochner integral (genuine, since a measurable function with bounded differences is bounded).
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 503, Theorem 2 (McDiarmid, 1989)

import Mathlib
import Definitions.Def_StabGen_Hypothesis_Setting

open MeasureTheory

namespace StabGen.Uniform

/-- **McDiarmid's inequality** (Bousquet & Elisseeff 2002, Theorem 2, p. 503; McDiarmid 1989).
Let `F : Z^m → ℝ` be measurable with bounded differences `|F(S) − F(S^i)| ≤ c_i` for every sample
`S`, every index `i` and every replacement point `z'_i`. Then for every `ε > 0`,
`P_S[F(S) − E_S[F(S)] ≥ ε] ≤ exp(−2ε² / ∑_{i=1}^m c_i²)`, where `S ∼ D^m`.
The printed upper summation index `n` is a slip for `m`. At zero total squared
difference, the tail probability is zero (the continuous extension of the bound). -/
theorem mcdiarmid_inequality {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (F : (Fin m → Z) → ℝ) (hF : Measurable F)
    (c : Fin m → ℝ)
    (hc : ∀ (S : Fin m → Z) (i : Fin m) (z' : Z), |F S - F (StabGen.Hypothesis.replaceAt S i z')| ≤ c i)
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m => D)
        {S | ε ≤ F S - ∫ S', F S' ∂(Measure.pi fun _ : Fin m => D)}
      ≤ if (∑ i, c i ^ 2) = 0 then 0
        else ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / ∑ i, c i ^ 2)) := by sorry

end StabGen.Uniform
