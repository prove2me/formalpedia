-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_3
-- name    : SparseCCE.ThreePlayer.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:13.308794+00:00
-- url     : https://prove2.me/theorems/4c201551-943c-4ecc-9b03-30c61f10a5eb
-- title:
--   Lemma 3.3 — transfer of one-round gains under $P\le CQ$
-- statement:
--   Let $O$ be a finite set, $H\ge1$, and $P,Q\in\Delta(O^H)$ with $P\le CQ$ pointwise for some $C\ge1$. Let $g(h,\sigma,o)\in[-1,1]$ be a function of a round, a history $\sigma\in O^{h-1}$ and an outcome, and let $\beta\in\mathbb R$ satisfy $E_Q[g(\sigma_h,o_h)\mid\sigma_h=\sigma]\ge\beta$ for every round $h$ and every history $\sigma$ with $Q(\sigma_h=\sigma)>0$. Then
--   $$E_P\Big[\frac1H\sum_{h=1}^Hg(\sigma_h,o_h)\Big]\ge\beta-\sqrt{2\log(C)/H}.$$
--
--   Differences from the source:
--   - encoding: H rounds, H implicit and positive (the bound divides by H) → an explicit hypothesis 1 ≤ H; reason: the statement is undefined at H = 0; Lean’s x/0 = 0 would give a different, false claim there
--   - encoding: g a function of a history and an outcome; the conditional expectation given σ_h = σ → g indexed by the round and the history (a history determines its round); the conditional expectation as a ratio for histories of positive Q-probability; reason: same functions and the same realizable histories
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.3, p. 15; proof App. A.2, pp. 28–29.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame

namespace SparseCCE.ThreePlayer

/-- **Lemma 3.3 (Transfer of one-round gains)**, p. 15: let `P, Q ∈ Δ(Ω)` with `P ≤ C Q` for some
`C ≥ 1`, let `g` be a function of a history and an outcome with values in `[−1, 1]`, and let `β`
be such that `E_Q[g(σ_h, o_h) | σ_h = σ] ≥ β` for every round `h` and every history `σ` realizable
under `Q`. Then `E_P[(1/H) ∑_h g(σ_h, o_h)] ≥ β − √(2 log(C)/H)`. -/
theorem lemma_3_3 {O : Type} [Fintype O] [DecidableEq O] (H : ℕ) (hH : 1 ≤ H)
    (P Q : (Fin H → O) → ℝ) (hP : IsDist P) (hQ : IsDist Q) (C : ℝ) (hC : 1 ≤ C)
    (hPQ : ∀ ω, P ω ≤ C * Q ω) (g : (h : Fin H) → (Fin h.val → O) → O → ℝ)
    (hg : ∀ h σ o, -1 ≤ g h σ o ∧ g h σ o ≤ 1) (β : ℝ)
    (hβ : ∀ (h : Fin H) (σ : Fin h.val → O),
      0 < ∑ ω, (if histOf ω h = σ then Q ω else 0) →
      β ≤ (∑ ω, if histOf ω h = σ then Q ω * g h σ (ω h) else 0) /
        ∑ ω, (if histOf ω h = σ then Q ω else 0)) :
    β - Real.sqrt (2 * Real.log C / H) ≤
      ∑ ω, P ω * ((1 / (H : ℝ)) * ∑ h, g h (histOf ω h) (ω h)) := by sorry

end SparseCCE.ThreePlayer
