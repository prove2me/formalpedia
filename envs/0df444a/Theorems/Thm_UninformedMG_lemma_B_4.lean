-- Prove2me | Theorems.Thm_UninformedMG_lemma_B_4
-- name    : UninformedMG.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:48.023781+00:00
-- url     : https://prove2.me/theorems/1312aa34-21ad-4d52-8445-6a6622afa196
-- title:
--   Lemma B.4 — with probability $1-\delta/2$, the estimation bound (31) for all $(v,x)$
-- statement:
--   Consider a run of Algorithm 1 on the grid $\mathcal V$ with $0<\lambda\le1/(2S)$, against any adaptive opponent, with $|A_h|\le A$, and let $\delta\in(0,1)$. With probability at least $1-\delta/2$, for every candidate $v\in\mathcal V$ and every mixed Markov policy $x$,
--   $$\sum_{k=1}^K\sum_{h=1}^H\frac{q^k_h(v\mid s^k_h)}{w^k(v)}\sum_ax_h(a\mid s^k_h)\Big(\widehat Y^k_{h,s^k_h,v,a}-Y^k_{h,s^k_h,v,a}\Big)\le\frac{\log|\mathcal V|+S\log A+\log(2/\delta)}\lambda.\tag{31}$$
--
--   Here $\widehat Y^k$ is the implicit-exploration estimator (21) on the realized trajectory and $Y^k$ its target. This is where the bias of implicit exploration gives a high-probability bound rather than one in expectation.
--
--   Differences from the source:
--   - generalization: Algorithm 1 run with the λ of Theorem 2.1, the learner computing q^k from its own observations → any run with 0 < λ ≤ 1/(2S) and any F^k-measurable selection q^k of the argmin in (23); reason: the theorem's λ lies in this range since A + 1 ≥ 1, and every learner selection is an F^k-measurable selection
--   - generalization: A = |⋃_h A_h| → any A with |A_h| ≤ A for every step h; reason: the proof uses only |A_h| ≤ A (union bound over A^S policies, S log A, |A_h| ≤ A in Lemma B.6); the paper's A is one such bound
--   - encoding: with probability at least 1 − δ/2 → the outer measure of the bad event is at most δ/2; reason: no measurability of the event is needed; for a measurable event the two agree
--   - encoding: the adaptive-opponent protocol of Section 1.1 → an Interaction: lexicographic history filtration, measurability of states, actions, policies, and the conditional step law; reason: this is the protocol's formal content; the natural history filtration is an instance
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Lemma B.4, p.20 (PDF p.22), proof pp.20–21

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_potQ
open MeasureTheory

namespace UninformedMG

/-- **Lemma B.4** (p.20 = PDF p.22; proof to p.21). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

With probability at least `1 − δ/2`, for every candidate `v ∈ V` and every mixed Markov policy `x`,
`∑_{k=1}^K ∑_{h=1}^H (q^k_h(v|s^k_h)/w^k(v)) ∑_a x_h(a|s^k_h)(Ŷ^k_{h,s^k_h,v,a} − Y^k_{h,s^k_h,v,a})
≤ (log|V| + S log A + log(2/δ))/λ` (31).

**Formalization Note.** One bad event with `(v, x)` inside; outer measure at most `δ/2`. `Ŷ^k` is
Eq. (21) on the realized trajectory, `Y^k = Ytab G ν^k`. -/
theorem lemma_B_4 {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Interaction G K Ω P)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (R : Run (grid G K) lam I) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | ∃ (v : (grid G K).C) (x : LPolicy G), IsLPolicy G x ∧
      (Real.log (Fintype.card (grid G K).C) + (G.numStates : ℝ) * Real.log A + Real.log (2 / δ)) / lam <
        ∑ k : Fin K, ∑ h : Fin H, R.q k ω h (I.st k h.castSucc ω) v / R.w k.castSucc ω v *
          ∑ a, x h (I.st k h.castSucc ω) a *
            (Yhat (grid G K) lam (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.q k ω) (I.traj k ω) h
                (I.st k h.castSucc ω) v a -
              Ytab G (I.opol k ω) ((grid G K).val v) h (I.st k h.castSucc ω) a)} ≤
      ENNReal.ofReal (δ / 2) := by sorry

end UninformedMG
