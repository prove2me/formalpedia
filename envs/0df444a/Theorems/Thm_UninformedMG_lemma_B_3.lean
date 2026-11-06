-- Prove2me | Theorems.Thm_UninformedMG_lemma_B_3
-- name    : UninformedMG.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:06.363095+00:00
-- url     : https://prove2.me/theorems/cfb29472-5306-4060-83d4-0c7301395003
-- title:
--   Lemma B.3 — with probability $1-\delta/2$, the OMD regret bound (30) for all $(v,x)$
-- statement:
--   Consider a run of Algorithm 1 on the grid $\mathcal V$ with $0<\lambda\le1/(2S)$, against any adaptive opponent, with $|A_h|\le A$, and let $\delta\in(0,1)$. With probability at least $1-\delta/2$, for every candidate $v\in\mathcal V$ and every mixed Markov policy $x$,
--   $$\sum_{k=1}^K\big(L^k-\langle z^{v,x},g^k\rangle\big)\le\frac{H\log|\mathcal V|+S\log A+H\log(2/\delta)}\lambda+2(A+1)S\lambda K,\tag{30}$$
--   where $L^k=V^{\mu^k,\nu^k}_1(s^k_1)/H$ and $z^{v,x}_{h,s,v',a}=\mathbf 1\{v'=v\}x_h(a\mid s)$.
--
--   The event does not depend on $(v,x)$, so the bound holds simultaneously for all comparators, including data-dependent ones such as the $(v^\dagger,\mu^{\mathrm{emp}})$ of the main proof.
--
--   Differences from the source:
--   - generalization: Algorithm 1 run with the λ of Theorem 2.1, the learner computing q^k from its own observations → any run with 0 < λ ≤ 1/(2S) and any F^k-measurable selection q^k of the argmin in (23); reason: the theorem's λ lies in this range since A + 1 ≥ 1, and every learner selection is an F^k-measurable selection
--   - generalization: A = |⋃_h A_h| → any A with |A_h| ≤ A for every step h; reason: the proof uses only |A_h| ≤ A (union bound over A^S policies, S log A, |A_h| ≤ A in Lemma B.6); the paper's A is one such bound
--   - encoding: with probability at least 1 − δ/2 → the outer measure of the bad event is at most δ/2; reason: no measurability of the event is needed; for a measurable event the two agree
--   - encoding: the adaptive-opponent protocol of Section 1.1 → an Interaction: lexicographic history filtration, measurability of states, actions, policies, and the conditional step law; reason: this is the protocol's formal content; the natural history filtration is an instance
--   - encoding: L^k = E^k[Σ_h ℓ^k_h/H] → L^k := V^{μ^k,ν^k}_1(s^k_1)/H; reason: the paper's identity (p.26); same quantity
--   - encoding: z ∈ 𝒵 → the pair (w, π) of Eq. (4); reason: every z ∈ 𝒵 is w·π and every quantity used is unchanged by π at w(v) = 0
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Lemma B.3, p.19 (PDF p.21), proof pp.19–20

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_potQ
open MeasureTheory

namespace UninformedMG

/-- **Lemma B.3** (p.19 = PDF p.21; proof to p.20). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

With probability at least `1 − δ/2`, for every candidate `v ∈ V` and every mixed Markovian policy `x`,
`∑_{k=1}^K (L^k − ⟨z^{v,x}, g^k⟩) ≤ (H log|V| + S log A + H log(2/δ))/λ + 2(A+1)SλK` (30),
where `L^k = V^{μ^k,ν^k}_1(s^k_1)/H`.

**Formalization Note.** The bad event is one set, with `(v, x)` quantified inside it; its outer
measure is at most `δ/2`. The run is any run of Algorithm 1 with `0 < λ ≤ 1/(2S)`. -/
theorem lemma_B_3 {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Interaction G K Ω P)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (R : Run (grid G K) lam I) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | ∃ (v : (grid G K).C) (x : LPolicy G), IsLPolicy G x ∧
      ((H : ℝ) * Real.log (Fintype.card (grid G K).C) + (G.numStates : ℝ) * Real.log A +
          (H : ℝ) * Real.log (2 / δ)) / lam + 2 * ((A : ℝ) + 1) * G.numStates * lam * K <
        ∑ k : Fin K, (value G (I.lpol k ω) (I.opol k ω) 0 (I.st k 0 ω) / (H : ℝ) -
          pairing (grid G K) (cmpW (grid G K) v) (cmpPi (grid G K) x) (R.g k ω))} ≤
      ENNReal.ofReal (δ / 2) := by sorry

end UninformedMG
