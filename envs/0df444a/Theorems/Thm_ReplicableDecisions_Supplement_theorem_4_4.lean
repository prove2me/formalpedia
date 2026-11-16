-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_4_4
-- name    : ReplicableDecisions.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:06:00.701838+00:00
-- url     : https://prove2.me/theorems/d55c94bb-9476-4be0-803d-8a6db1a50ad4
-- title:
--   Theorem 4.4 — strong replication for early-versus-late change points
-- statement:
--   For the change-point experiment (4.1), let $n^\star_{\mathrm{str}}(\beta,\rho)$ be the optimal sample size when accuracy is required at the models $P_0,\dots,P_d$ and replication under every distribution on $\{0,1\}^d$ (including laws with arbitrary dependence among coordinates).
--
--   There are absolute constants $C_1,C_2>0$ such that for every integer $d\ge1$, $0<c\le1/4$, $0<\beta\le1/8$ and $0<\rho\le1/16$,
--   $$C_1F\le n^\star_{\mathrm{str}}(\beta,\rho)\le C_2F,\qquad F=c^{-2}\Big[\rho^{-2}+\log\frac1\beta\Big].$$
--   Moreover, with
--   $$k=\Big\lceil\frac9{2\rho^2}\Big\rceil,\qquad m=\Big\lceil\frac2{c^2}\Big(\log8+\frac3k\log\frac1\beta\Big)\Big\rceil,$$
--   a strongly $(\beta,\rho)$-valid rule exists with $n=km$ samples, one sample being one whole coordinate vector.
--
--   Compared with Theorem 4.2, the exponent of $1/\rho$ in the replication cost is $2$ under strong and $1$ under weak replication in the dense regime $d\rho\ge1$.
--
--   Differences from the source:
--   - encoding: n⋆_str(β, ρ) = Θ(c⁻²[ρ⁻² + log(1/β)]) with absolute (uniform) implicit constants → ∃ C₁ C₂ > 0, quantified before every parameter, with C₁·F ≤ N ≤ C₂·F for the least element N; reason: the Lean reading of Θ with constants independent of all displayed parameters
--   - encoding: n⋆_str: accuracy at the models, replication under every distribution on {0, 1}^d → least element of strongValidSampleSizes: err ≤ β at the d + 1 models, repDist q ≤ ρ for every q ∈ stdSimplex ℝ (Fin d → Bool); reason: the paper's contract (p.20, p.41) in the Lean model
--   - reading: "A strongly replicable rule with accuracy error at most β uses n = km samples" → k·m ∈ strongValidSampleSizes (a strongly (β, ρ)-valid rule exists with km samples); reason: "strongly replicable" at the theorem's ρ, as the proof shows (replication error ≤ ρ for every Q)
--   - encoding: Z = {0, 1}^d, models P_0, …, P_d → Fin d → Bool, models indexed by Fin (d + 1); reason: Lean indexing; the same laws
--   - reading: "Its data processing uses O(kmd) integer arithmetic operations and one shared random threshold comparison" → not formalized; reason: names no machine model; implementation remark, as for the published Theorem 3.2
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 4.4, (4.15)–(4.16), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ReplicableDecisions_Supplement_strongValidSampleSizes
import Definitions.Def_ReplicableDecisions_Supplement_changePoint

namespace ReplicableDecisions.Supplement

/-- **Theorem 4.4 (Strong replication for early-versus-late change points).** Chen, *Replicable
Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 4.4,
(4.15)–(4.16), p.20 (PDF p.22). For every integer `d ≥ 1`, `0 < c ≤ 1/4`, `0 < β ≤ 1/8` and
`0 < ρ ≤ 1/16`, the experiment (4.1) satisfies `n⋆_str(β, ρ) = Θ(c⁻²[ρ⁻² + log(1/β)])`, all
implicit constants absolute and uniform; with `k = ⌈9/(2ρ²)⌉` and
`m = ⌈(2/c²)(log 8 + (3/k) log(1/β))⌉`, a strongly replicable rule with accuracy error at most `β`
uses `n = km` samples.

**Formalization Note.** `N` is `n⋆_str` (`IsLeast` of `strongValidSampleSizes`): accuracy at the
`d + 1` models, replication under every probability vector on `{0, 1}^d`. The `O(kmd)` operation
count is not formalized. -/
theorem theorem_4_4 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc₀ : 0 < c) (hc : c ≤ 1 / 4) (β ρ : ℝ),
        0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
        let F : ℝ := (1 / c ^ 2) * (1 / ρ ^ 2 + Real.log (1 / β))
        let k : ℕ := ⌈9 / (2 * ρ ^ 2)⌉₊
        let m : ℕ := ⌈2 / c ^ 2 * (Real.log 8 + 3 / (k : ℝ) * Real.log (1 / β))⌉₊
        ∃ N : ℕ,
          IsLeast (strongValidSampleSizes (changePoint d c hd hc₀ hc) (earlyLateΓ d) β ρ) N ∧
          C₁ * F ≤ (N : ℝ) ∧ (N : ℝ) ≤ C₂ * F ∧
          k * m ∈ strongValidSampleSizes (changePoint d c hd hc₀ hc) (earlyLateΓ d) β ρ := by sorry

end ReplicableDecisions.Supplement
