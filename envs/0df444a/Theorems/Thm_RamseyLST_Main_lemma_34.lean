-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_34
-- name    : RamseyLST.Main.lemma_34
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:07.609042+00:00
-- url     : https://prove2.me/theorems/12aa0d3b-4133-4a9a-ace4-67af7f000fe3
-- title:
--   Lemma 34 — the Case 1 ratio bound: some $i \in [t]$ satisfies inequality (6)
-- statement:
--   Let $\sigma>1$, let $t\ge8$ be an integer, and let $\Phi\ge\sigma^2$. Let $Z^{in}$ be a finite candidate core with a nonnegative weight function $w$, where $w(Q)=\sum_{z\in Q\cap Z^{in}}w(z)$. Let $Q_0\subseteq Q_1\subseteq\dots\subseteq Q_t$ be sets with $w(Q_0)>0$. With $\psi_1(\Phi)=(t\log_\sigma\Phi)^{-2/t}$, there is an $i\in\{1,\dots,t\}$ with
--
--   $$w(Q_{i-1})^{\psi_1(\Phi/\sigma)}\ \ge\ w(Q_i)\cdot w(Q_t)^{\psi_1(\Phi)-1}\cdot w(Q_0)^{\psi_1(\Phi/\sigma)-\psi_1(\Phi)}.\tag{6}$$
--
--   This is the bound for Case 1 of CreatePetal (all nearby candidate core points light): the radius index $i$ chosen by the algorithm satisfies (6), which pays for the discarded core points with the slack between $\psi_1(\Phi/\sigma)$ and $\psi_1(\Phi)$.
--
--   Differences from the source:
--   - generalization: σ = 800, the absolute constant of Remark 1 → every real σ > 1; reason: the proof uses only a = log_σ(Φ/σ) ≥ 1, which follows from Φ ≥ σ²; the statement specializes to σ = 800
--   - generalization: w : Z^in → ℝ>0 (the positive weights handled by CreatePetal, p. 38) → w nonnegative on Z^in; reason: only the values w(Q_i) enter, and w(Q_0) > 0 is assumed; positive weights are a special case
--   - reading: sets Q_0 ⊆ … ⊆ Q_t and i ∈ [t] → t a natural number, sets Q 0, …, Q t (a function ℕ → Finset whose values beyond t are unused), i ∈ {1, …, t}; reason: the indexing Q_0, …, Q_t and [t] = {1, …, t} requires an integer t, and the proof iterates over i = 1, …, t
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 48 (PDF 52), Lemma 34

import Mathlib
import Definitions.Def_RamseyLST_Main_Weights

namespace RamseyLST.Main

/-- Lemma 34 (p. 48): let `σ > 1`, `t ≥ 8`, `Φ ≥ σ²`, and let `Q₀ ⊆ Q₁ ⊆ ⋯ ⊆ Q_t` with
`w(Q₀) > 0`, where `w(Q) = ∑_{z ∈ Q ∩ Zin} w(z)` for a nonnegative weight function on the
candidate core `Zin`. Then some `i ∈ {1, …, t}` satisfies
`w(Q_{i−1})^{ψ₁(Φ/σ)} ≥ w(Q_i) · w(Q_t)^{ψ₁(Φ)−1} · w(Q₀)^{ψ₁(Φ/σ)−ψ₁(Φ)}`. -/
theorem lemma_34 (σ : ℝ) (hσ : 1 < σ) (t : ℕ) (ht : 8 ≤ t) (Φ : ℝ) (hΦ : σ ^ 2 ≤ Φ)
    (ι : Type) [DecidableEq ι] (Zin : Finset ι) (w : ι → ℝ) (hw : ∀ z ∈ Zin, 0 ≤ w z)
    (Q : ℕ → Finset ι) (hQ : ∀ i < t, Q i ⊆ Q (i + 1)) (hQ0 : 0 < setWeight Zin w (Q 0)) :
    ∃ i ∈ Finset.Icc 1 t,
      setWeight Zin w (Q i) * setWeight Zin w (Q t) ^ (psi1 σ t Φ - 1) *
          setWeight Zin w (Q 0) ^ (psi1 σ t (Φ / σ) - psi1 σ t Φ) ≤
        setWeight Zin w (Q (i - 1)) ^ psi1 σ t (Φ / σ) := by sorry

end RamseyLST.Main
