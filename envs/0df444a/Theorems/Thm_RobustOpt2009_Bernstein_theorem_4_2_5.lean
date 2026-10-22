-- Prove2me | Theorems.Thm_RobustOpt2009_Bernstein_theorem_4_2_5
-- name    : RobustOpt2009.Bernstein.theorem_4_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:41:46.431105+00:00
-- url     : https://prove2.me/theorems/20a9de2f-0e58-438f-9665-ee515c31eb27
-- title:
--   Theorem 4.2.5 — the Bernstein uncertainty set
-- statement:
--   Let $P$ be a probability distribution on $\mathbb R^L$ and let $0<\epsilon<1$. Assume Q.1: the finite convex function $\Phi$ satisfies $\Phi(0)=0$ and $\log\mathbb E_P e^{\langle w,\zeta\rangle}\le\Phi(w)$ for every $w$. Assume Q.2: the convex lower semicontinuous function $\phi:\mathbb R^M\to\mathbb R\cup\{+\infty\}$ has bounded real sublevel sets and
--   $$\Phi(w)=\sup_u\{\langle w,Au+a\rangle-\phi(u)\}.$$
--   Then
--   $$U_\epsilon=\{u:\phi(u)\le\log(1/\epsilon)\}$$
--   is nonempty, convex, and compact. Define $\mathcal Z_\epsilon=A U_\epsilon+a$, and let $Z_\epsilon$ be the closed coefficient set in (4.2.5). For every $z=(z_0,w)$,
--   $$z\in Z_\epsilon\quad\Longleftrightarrow\quad z_0+\langle\zeta,w\rangle\le0\ \ \text{for every }\zeta\in\mathcal Z_\epsilon.$$
--   In particular,
--   $$z\in Z_\epsilon\quad\Longleftrightarrow\quad\inf_{\beta>0}\bigl[z_0+\beta\Phi(\beta^{-1}w)+\beta\log(1/\epsilon)\bigr]\le0,$$
--   The displayed perspective infimum is finite everywhere, as established in Proposition 4.2.2 through Lemma B.1.1, and this condition implies $P\{z_0+\langle w,\zeta\rangle>0\}\le\epsilon$. Thus the Bernstein sufficient condition is exactly robust feasibility for the displayed uncertainty set.
--
--   **Formalization Note** The coefficient cone and perturbation set have different types. The exponential-moment bound is encoded using a nonnegative integral, and the perspective infimum uses extended reals. Independence is not assumed, and closure is retained rather than replaced by the existence of a positive optimizing scale. The theorem expands Q.1–2 and the constructed sets directly, so the blind auditor can read every condition without opening imported modules.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 4.2.5, printed pp. 85–86 (PDF pp. 111–112)

import Mathlib

open MeasureTheory Set
open scoped BigOperators

namespace RobustOpt2009.Bernstein

theorem theorem_4_2_5 {L M : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ) (phi : (Fin M → ℝ) → EReal)
    (A : (Fin M → ℝ) →ₗ[ℝ] (Fin L → ℝ)) (a : Fin L → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hPhi : ConvexOn ℝ univ Phi) (hPhi0 : Phi 0 = 0)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w)))
    (hbot : ∀ u, phi u ≠ ⊥)
    (hconv : Convex ℝ {p : (Fin M → ℝ) × ℝ | phi p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c : ℝ, IsClosed {u | phi u ≤ (c : EReal)})
    (hbounded : ∀ c : ℝ, Bornology.IsBounded {u | phi u ≤ (c : EReal)})
    (hrep : ∀ w, (Phi w : EReal) =
      ⨆ u, ((∑ i, w i * (A u + a) i : ℝ) : EReal) - phi u) :
    let U : Set (Fin M → ℝ) := {u | phi u ≤ (Real.log (1 / ε) : EReal)}
    let Z : Set (ℝ × (Fin L → ℝ)) :=
      closure {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
    let V : (ℝ × (Fin L → ℝ)) → EReal := fun z =>
      ⨅ β : {b : ℝ // 0 < b},
        ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)
    U.Nonempty ∧ Convex ℝ U ∧ IsCompact U ∧
    (∀ z : ℝ × (Fin L → ℝ), z ∈ Z ↔
      ∀ ζ ∈ (fun u => A u + a) '' U, z.1 + ∑ i, ζ i * z.2 i ≤ 0) ∧
    (∀ z, ∃ r : ℝ, V z = (r : EReal)) ∧
    (∀ z, z ∈ Z ↔ V z ≤ 0) ∧
    (∀ z, V z ≤ 0 → P {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} ≤ ENNReal.ofReal ε) := by sorry

end RobustOpt2009.Bernstein
