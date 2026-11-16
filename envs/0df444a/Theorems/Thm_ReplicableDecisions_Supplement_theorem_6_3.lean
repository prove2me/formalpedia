-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_3
-- name    : ReplicableDecisions.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:09:01.804341+00:00
-- url     : https://prove2.me/theorems/6618b961-2011-406f-942e-eae6f98f9a05
-- title:
--   Theorem 6.3 — strong replication for noisy parities
-- statement:
--   For the noisy-parity experiment of Theorem 6.2 with $M=2^b$ models, let $n^\star_{\mathrm{str}}(\beta,\rho)$ require accuracy at the models and replication under every distribution on $\mathbb F_2^b$.
--
--   There are universal constants $C_1,C_2>0$ such that, uniformly over $b\ge1$, $0<\varepsilon\le1/2$, $0<\beta\le1/8$ and $0<\rho\le1/16$,
--   $$C_1\varepsilon^{-2}\Big[\rho^{-2}+\log\frac M\beta\Big]\le n^\star_{\mathrm{str}}(\beta,\rho)\le C_2\varepsilon^{-2}\Big[\rho^{-2}+\log\frac M\beta\Big],$$
--   and in particular
--   $$n^\star_{\mathrm{str}}(\beta,\rho)\le\Big\lceil\varepsilon^{-2}\max\Big\{8\log\frac M\beta,\ \frac4{\rho^2}\Big\}\Big\rceil.$$
--
--   Under strong replication the model count enters only through the confidence term.
--
--   Differences from the source:
--   - encoding: n⋆_str(β, ρ) = Θ(ε⁻²[ρ⁻² + log(M/β)]) uniformly with absolute (uniform) implicit constants → ∃ C₁ C₂ > 0, quantified before every parameter, with C₁·F ≤ N ≤ C₂·F for the least element N; reason: the Lean reading of Θ with constants independent of all displayed parameters
--   - encoding: replication under every distribution on F₂^b → repDist q ≤ ρ for every q ∈ stdSimplex ℝ (Fin b → ZMod 2) (strongValidSampleSizes); reason: the paper's contract in the Lean model
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.3, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_ReplicableDecisions_Supplement_strongValidSampleSizes
import Definitions.Def_ReplicableDecisions_Supplement_noisyParity

namespace ReplicableDecisions.Supplement

/-- **Theorem 6.3 (Strong replication for noisy parities).** Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 6.3, p.28 (PDF p.30). For the
noisy-parity experiment of Theorem 6.2, uniformly over `b ≥ 1`, `0 < ε ≤ 1/2`, `0 < β ≤ 1/8` and
`0 < ρ ≤ 1/16`, `n⋆_str(β, ρ) = Θ(ε⁻²[ρ⁻² + log(M/β)])`; in particular
`n⋆_str(β, ρ) ≤ ⌈ε⁻² max{8 log(M/β), 4/ρ²}⌉`.

**Formalization Note.** `N` is `n⋆_str`: accuracy at the `2^b` models, replication under every
probability vector on `F₂^b`. The constants are quantified before every parameter. -/
theorem theorem_6_3 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (b : ℕ), 1 ≤ b → ∀ (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) (β ρ : ℝ),
        0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
        let M : ℝ := Fintype.card (Fin b → ZMod 2)
        let F : ℝ := 1 / ε ^ 2 * (1 / ρ ^ 2 + Real.log (M / β))
        ∃ N : ℕ, IsLeast (strongValidSampleSizes (noisyParity b ε hε₀ hε) parityΓ β ρ) N ∧
          C₁ * F ≤ (N : ℝ) ∧ (N : ℝ) ≤ C₂ * F ∧
          N ≤ ⌈1 / ε ^ 2 * max (8 * Real.log (M / β)) (4 / ρ ^ 2)⌉₊ := by sorry

end ReplicableDecisions.Supplement
