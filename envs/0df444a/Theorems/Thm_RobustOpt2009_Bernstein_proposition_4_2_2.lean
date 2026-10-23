-- Prove2me | Theorems.Thm_RobustOpt2009_Bernstein_proposition_4_2_2
-- name    : RobustOpt2009.Bernstein.proposition_4_2_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:41:46.5099+00:00
-- url     : https://prove2.me/theorems/29835330-f012-4831-9380-51191ab5d8ab
-- title:
--   Proposition 4.2.2 — normal safety of the Bernstein approximation
-- statement:
--   Let $P$ be a probability distribution on $\mathbb R^L$, let $0<\epsilon<1$, and let $\Phi:\mathbb R^L\to\mathbb R$ satisfy Q.1: it is convex, $\Phi(0)=0$, and $\log\mathbb E_P e^{\langle w,\zeta\rangle}\le\Phi(w)$ for every $w$. With $Z_\epsilon$ the closure in (4.2.5),
--   $$Z_\epsilon=\left\{(z_0,w):\inf_{\beta>0}\bigl[z_0+\beta\Phi(\beta^{-1}w)+\beta\log(1/\epsilon)\bigr]\le0\right\}.$$
--   The function on the left of this inequality is finite everywhere and convex, and its zero sublevel set is a normal safe approximation of $P\{z_0+\langle w,\zeta\rangle>0\}\le\epsilon$.
--
--   Here normal safe means a closed convex cone contained in the chance-feasible set, with $(-1,0)$ interior and $(1,0)$ excluded, as in Remark 4.1.2. This includes the boundary points obtained through closure.
--
--   **Formalization Note** Q.1 is expressed by the equivalent exponential bound on the nonnegative integral. The infimum is computed in extended reals, with finiteness concluded explicitly as established by the source’s application of Lemma B.1.1 on printed p. 471 (PDF p. 497). No attaining positive scale is assumed. The hypotheses and sets are expanded directly for a self-contained blind read-back.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Proposition 4.2.2, printed p. 84 (PDF p. 110)

import Mathlib

open MeasureTheory Set
open scoped BigOperators

namespace RobustOpt2009.Bernstein

theorem proposition_4_2_2 {L : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hPhi : ConvexOn ℝ univ Phi) (hPhi0 : Phi 0 = 0)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w))) :
    let Z : Set (ℝ × (Fin L → ℝ)) :=
      closure {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
    let V : (ℝ × (Fin L → ℝ)) → EReal := fun z =>
      ⨅ β : {b : ℝ // 0 < b},
        ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)
    let S : Set (ℝ × (Fin L → ℝ)) := {z | V z ≤ 0}
    Z = S ∧ (∀ z, ∃ r : ℝ, V z = (r : EReal)) ∧
    Convex ℝ {p : (ℝ × (Fin L → ℝ)) × ℝ | V p.1 ≤ (p.2 : EReal)} ∧
    (∀ z ∈ S, P {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} ≤ ENNReal.ofReal ε) ∧
    IsClosed S ∧ Convex ℝ S ∧ (0 : ℝ × (Fin L → ℝ)) ∈ S ∧
    (∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S) ∧
    ((-1, 0) : ℝ × (Fin L → ℝ)) ∈ interior S ∧
    ((1, 0) : ℝ × (Fin L → ℝ)) ∉ S := by sorry

end RobustOpt2009.Bernstein
