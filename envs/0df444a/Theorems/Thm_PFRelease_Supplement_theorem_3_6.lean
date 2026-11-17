-- Prove2me | Theorems.Thm_PFRelease_Supplement_theorem_3_6
-- name    : PFRelease.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:45:46.974334+00:00
-- url     : https://prove2.me/theorems/f02d8216-9602-4884-95fa-a424f2a1cc65
-- title:
--   Theorem 3.6 — retention guarantee of the element–block filter, with $\bar\gamma=\sigma'\ln(2n/\beta)$, $\bar\eta=\sigma\ln(2/\beta)$
-- statement:
--   Let $n,b\in\mathbb N$ with $b>0$ dividing $n$, $\beta\in(0,1)$, $t,\kappa\ge0$, $\sigma,\sigma'>0$, a dataset $s\in\mathcal X^n$ and a friendliness predicate $F$. Fix any realization $\pi$ of the filter's partition of $[n]$ into blocks of size $b$, and let $c_i$ be the number of blocks of $\pi$ that $s_i$ is friendly with. Put
--   $$
--   \bar\gamma:=\sigma'\ln(2n/\beta),\qquad \bar\eta:=\sigma\ln(2/\beta).
--   $$
--   Then, with probability at least $1-\beta$ over the noises $\eta\sim\mathrm{Lap}(\sigma)$, $\gamma_1,\dots,\gamma_n\sim\mathrm{Lap}(\sigma')$ of the filter $\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F;s)$ (Algorithm 1), the following hold simultaneously:
--
--   1. **Retention.** If $|\{i:c_i\le t+\bar\gamma\}|<\kappa-\bar\eta$, then the run does not abort and retains every $s_i$ with $c_i>t+\bar\gamma$.
--   2. **Quality of retained records.** Every retained record $s_i$ satisfies $c_i>t-\bar\gamma$.
--
--   The theorem describes when the filter keeps the data instead of aborting, and certifies that whatever it keeps passed its friendliness test up to the noise margin $\bar\gamma$.
--
--   **Formalization Note** The run *aborts* when one of the two abort branches of Algorithm 1 fires: $\tilde\kappa=\lceil\kappa+\eta\rceil\le0$, or the sparse-vector transcript (the literal `svRun` used by the published `filterOut`) contains $\tilde\kappa$ failures. A slot $i$ is *retained* when it is not in the nulled set $I$ of the output $s^{I\to\perp}$. Both items are required on one event, and the measure of that event under $\mathrm{Lap}(\sigma)\otimes\mathrm{Lap}(\sigma')^{\otimes n}$ is bounded below.
--
--   Differences from the source:
--   - encoding: n, b ∈ ℕ under the standing assumption that b divides n (§3.1, p.8) → hypotheses 0 < b and b ∣ n; reason: the paper assumes throughout that b divides n, and blocks of size b need b > 0
--   - encoding: with probability over the noises, conditionally on any realization of the partition → for every equipartition π of [n] into blocks of size b, the measure under Lap(σ) ⊗ Lap(σ′)^{⊗n} of the event; reason: the noises are independent of the partition, so conditioning on π leaves exactly this noise law
--   - encoding: the run does not abort, s_i is retained → neither abort branch of Algorithm 1 fires (⌈κ + η⌉ ≤ 0, or the transcript has ⌈κ + η⌉ failures); i ∉ filterOut b t κ F s π η γ; reason: the literal branches of the published encoding of Algorithm 1
--   - reading: every retained record s_i (item 2), every s_i with c_i > t + γ̄ (item 1) → every slot i, null slots included; reason: records range over the domain augmented with ⊥ (§2), and the proof's argument (a retained slot passed its noisy test) covers every slot
--   - encoding: probability at least 1 − β → ENNReal.ofReal (1 − β) ≤ the measure of the event; reason: Lean convention; the event is cut out by finitely many comparisons of the noises
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 3.6, pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_PFRelease_filterLaw

open MeasureTheory

namespace PFRelease.Supplement

/-- **Theorem 3.6 (Retention guarantee)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private
Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 3.6, pp.10–11 = PDF pp.12–13).
Given `n, b ∈ ℕ`, `β ∈ (0, 1)`, `t, κ ≥ 0`, `σ, σ′ > 0`, a dataset `s ∈ Xⁿ` and a friendliness predicate
`F`, with probability at least `1 − β` over the noises of the filter `F_{b,t,κ,σ,σ′}(F; s)` (Algorithm 1),
conditionally on any realization `π` of its partition, the following hold simultaneously, where `cᵢ`
is the number of blocks of `π` that `sᵢ` is friendly with, `γ̄ := σ′ ln(2n/β)` and `η̄ := σ ln(2/β)`:
1. if `|{i : cᵢ ≤ t + γ̄}| < κ − η̄`, then the run does not abort and retains every `sᵢ` with
   `cᵢ > t + γ̄`;
2. every retained record `sᵢ` satisfies `cᵢ > t − γ̄`.

**Formalization Note** The noises are `(η, γ) ∼ Lap(σ) ⊗ Lap(σ′)^{⊗n}`, the noise law of the published
`filterLaw`; the partition is any equipartition `π` into blocks of size `b` (conditioning on it). The
run *aborts* iff one of the two abort branches of Algorithm 1 fires: `κ̃ = ⌈κ + η⌉ ≤ 0`, or the
sparse-vector transcript (the literal `svRun` inside `filterOut`) has `κ̃` failures. Slot `i` is
*retained* iff `i ∉ I`, where `s^{I→⊥}` is the output (`filterOut`). Both items hold on one event,
whose measure is bounded below. `b > 0`, `b ∣ n` are the standing assumption of §3.1 (p.8). -/
theorem theorem_3_6 {X : Type*} (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n) (β t κ σ σ' : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (ht : 0 ≤ t) (hκ : 0 ≤ κ) (hσ : 0 < σ) (hσ' : 0 < σ')
    (s : Fin n → Option X) (F : List (Option X) → Option X → Bool)
    (π : Fin n → Fin (n / b)) (hπ : π ∈ equipartitions n b) :
    let γbar := σ' * Real.log (2 * n / β)
    let ηbar := σ * Real.log (2 / β)
    let c : Fin n → ℕ := fun i => friendCount F π s (s i)
    ENNReal.ofReal (1 - β) ≤
      ((PrivLearn.Generic.laplace σ).prod
          (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace σ'))
        {ω : ℝ × (Fin n → ℝ) |
          let I := filterOut b t κ F s π ω.1 ω.2;
          let aborts : Prop := (⌈κ + ω.1⌉ ≤ 0 ∨
            ((List.count true (svRun t (⌈κ + ω.1⌉).toNat
                (fun i _ w => (friendCount F π w (s i) : ℝ)) s ω.2) : ℕ) : ℤ) = ⌈κ + ω.1⌉);
          ((((Finset.univ.filter fun i => (c i : ℝ) ≤ t + γbar).card : ℝ) < κ - ηbar →
              ¬ aborts ∧ ∀ i, t + γbar < (c i : ℝ) → i ∉ I) ∧
            (∀ i, i ∉ I → t - γbar < (c i : ℝ)))} := by sorry

end PFRelease.Supplement
