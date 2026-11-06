-- Prove2me | Theorems.Thm_UninformedMG_pathwise_regret_bound
-- name    : UninformedMG.pathwise_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:19.444057+00:00
-- url     : https://prove2.me/theorems/cf719bce-6e28-4c96-b4df-b8a2f0e7391f
-- title:
--   p.26 — on the event of (30) and (31): $\mathrm{Enr}_K/H\le (H-1)/H+C_\delta/\lambda+2(A+1)S\lambda K$
-- statement:
--   Consider a run of Algorithm 1 on the grid $\mathcal V$ with $0<\lambda\le1/(2S)$, with $|A_h|\le A$, and let $\delta\in(0,1)$. At any outcome where the bound (30) of Lemma B.3 and the bound (31) of Lemma B.4 hold for every candidate $v\in\mathcal V$ and every mixed Markov policy $x$,
--   $$\frac{\mathrm{Enr}_K}H=\sum_{k=1}^K\Big(L^k-\frac{V^{\mathrm{emp}}_1(s^k_1)}H\Big)\le\frac{H-1}H+\frac{C_\delta}\lambda+2(A+1)S\lambda K,$$
--   with $C_\delta=(H+1)\log N+2S\log A+(H+1)\log(2/\delta)$, $N=|\mathcal V|$, $L^k=V^{\mu^k,\nu^k}_1(s^k_1)/H$ and $V^{\mathrm{emp}}$ computed from the realized opponent policies.
--
--   Theorem 2.1 follows from this by a union bound over Lemmas B.3 and B.4 and the choice of $\lambda$.
--
--   Differences from the source:
--   - generalization: Algorithm 1 run with the λ of Theorem 2.1, the learner computing q^k from its own observations → any run with 0 < λ ≤ 1/(2S) and any F^k-measurable selection q^k of the argmin in (23); reason: the theorem's λ lies in this range since A + 1 ≥ 1, and every learner selection is an F^k-measurable selection
--   - generalization: A = |⋃_h A_h| → any A with |A_h| ≤ A for every step h; reason: the proof uses only |A_h| ≤ A (union bound over A^S policies, S log A, |A_h| ≤ A in Lemma B.6); the paper's A is one such bound
--   - encoding: "combining this bound with Eq. (30)" on the high-probability event → (30) and (31) for all (v, x) as hypotheses at a fixed outcome ω; reason: this is the pathwise step of the proof; the event is supplied by Lemmas B.3 and B.4
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), proof of Theorem 2.1, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_potQ
import Definitions.Def_UninformedMG_cDelta
open MeasureTheory

namespace UninformedMG

/-- **Pathwise regret bound in the proof of Theorem 2.1** (p.26 = PDF p.28). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

On an outcome where the conclusions (30) of Lemma B.3 and (31) of Lemma B.4 hold for every candidate
and every mixed Markov policy, "combining this bound with Eq. (30) and using
`L^k = V^{μ^k,ν^k}_1(s^k_1)/H` gives
`Enr_K/H = ∑_{k=1}^K (L^k − V^emp_1(s^k_1)/H) ≤ (H − 1)/H + C_δ/λ + 2(A+1)SλK`", with `C_δ` of
Theorem 2.1.

**Formalization Note.** Stated for one outcome `ω` of any run with `0 < λ ≤ 1/(2S)`; the opponent
policies, initial states and played policies are the realized ones. -/
theorem pathwise_regret_bound {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (I : Interaction G K Ω P)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (R : Run (grid G K) lam I) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ω : Ω)
    (h30 : ∀ (v : (grid G K).C) (x : LPolicy G), IsLPolicy G x →
      ∑ k : Fin K, (value G (I.lpol k ω) (I.opol k ω) 0 (I.st k 0 ω) / (H : ℝ) -
          pairing (grid G K) (cmpW (grid G K) v) (cmpPi (grid G K) x) (R.g k ω)) ≤
        ((H : ℝ) * Real.log (Fintype.card (grid G K).C) + (G.numStates : ℝ) * Real.log A +
          (H : ℝ) * Real.log (2 / δ)) / lam + 2 * ((A : ℝ) + 1) * G.numStates * lam * K)
    (h31 : ∀ (v : (grid G K).C) (x : LPolicy G), IsLPolicy G x →
      ∑ k : Fin K, ∑ h : Fin H, R.q k ω h (I.st k h.castSucc ω) v / R.w k.castSucc ω v *
          ∑ a, x h (I.st k h.castSucc ω) a *
            (Yhat (grid G K) lam (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.q k ω) (I.traj k ω) h
                (I.st k h.castSucc ω) v a -
              Ytab G (I.opol k ω) ((grid G K).val v) h (I.st k h.castSucc ω) a) ≤
        (Real.log (Fintype.card (grid G K).C) + (G.numStates : ℝ) * Real.log A + Real.log (2 / δ)) / lam) :
    enr G (fun k => I.lpol k ω) (fun k => I.opol k ω) (fun k => I.st k 0 ω) / (H : ℝ) ≤
      ((H : ℝ) - 1) / H + cDelta H G.numStates (Fintype.card (grid G K).C) A δ / lam +
        2 * ((A : ℝ) + 1) * G.numStates * lam * K := by sorry

end UninformedMG
