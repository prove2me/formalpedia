-- Prove2me | Theorems.Thm_RadGauss_Classification_mcdiarmid_step
-- name    : RadGauss.Classification.mcdiarmid_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:46:18.301614+00:00
-- url     : https://prove2.me/theorems/5f582762-75b7-4614-b689-d4a83d6e5f24
-- title:
--   Appendix B — w.p. ≥ 1 − δ, every f in F has P(Y ≠ f(X)) ≤ P̂_n(Y ≠ f(X)) + E sup_{h∈L∘F}(Eh − Ê_nh) + √(ln(1/δ)/(2n))
-- statement:
--   Let $P$ be a probability distribution on $\mathcal X \times \{\pm1\}$, $F$ a nonempty set of measurable $\{\pm1\}$-valued functions on $\mathcal X$, $n \ge 1$, and $0 < \delta < 1$. Let $S = ((X_i, Y_i))_{i=1}^n$ be drawn from $P^n$, let $\mathcal L(Y, f(X)) = \mathbf 1(Y \ne f(X))$ be the 0–1 loss, and write
--   $$\Phi(S) = \sup_{h \in \mathcal L \circ F}\big(\mathbb E h - \hat{\mathbb E}_n h\big) = \sup_{f \in F}\big(P(Y \ne f(X)) - \hat P_n(Y \ne f(X))\big).$$
--   Then with probability at least $1 - \delta$, every $f \in F$ satisfies
--
--   $$P(Y \ne f(X)) \le \hat P_n(Y \ne f(X)) + \mathbb E\,\Phi(S) + \sqrt{\frac{\ln(1/\delta)}{2n}} .$$
--
--   Precisely, the $P^n$-probability of the event that some $f \in F$ violates this inequality is at most $\delta$. This is the concentration half of the proof of Theorem 5(b); the remaining half bounds $\mathbb E\,\Phi(S)$ by $R_n(F)/2$.
--
--   **Formalization Note** The map $S \mapsto \Phi(S)$ is assumed measurable (the paper does not discuss measurability; McDiarmid's inequality needs a genuine expectation of $\Phi$, and $\Phi$ is bounded, so the expectation is a Bochner integral of a bounded measurable function). The hypotheses $n \ge 1$, $0 < \delta < 1$ and $F \ne \emptyset$ are the reading of the page's "with probability at least $1-\delta$" and "every $f \in F$". The bad event is a union over $F$ and is measured by the outer measure of $P^n$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 480 (PDF p. 18), Appendix B (Proof of Theorem 5), second display

import Mathlib
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **McDiarmid step for the 0–1 loss** (Bartlett–Mendelson 2002, Appendix B, p. 480, second
display). With probability at least `1 − δ` over an i.i.d. sample `S ∼ P^n`, every `f ∈ F`
satisfies `P(Y ≠ f(X)) ≤ P̂_n(Y ≠ f(X)) + E sup_{h ∈ L∘F}(E h − Ê_n h) + √(ln(1/δ)/(2n))`.
The bad event (some `f ∈ F` violates the bound) has `P^n`-(outer) measure at most `δ`.
Measurability guard: the supremum `S ↦ gapSup P F S` is measurable (so its expectation is a
genuine Bochner integral of a bounded measurable function). -/
theorem mcdiarmid_step {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (classError P f ≤ trainError S f
            + (∫ S', gapSup P F S' ∂(Measure.pi fun _ : Fin n => P))
            + Real.sqrt (Real.log (1 / δ) / (2 * n)))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.Classification
