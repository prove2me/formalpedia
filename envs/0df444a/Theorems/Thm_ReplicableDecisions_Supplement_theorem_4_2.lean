-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_4_2
-- name    : ReplicableDecisions.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:05:06.086835+00:00
-- url     : https://prove2.me/theorems/c39bb1b8-d07c-4016-87dd-977a2c885689
-- title:
--   Theorem 4.2 — sharp sample size for early-versus-late change points
-- statement:
--   Consider the change-point experiment (4.1): for an integer $d\ge1$ and $0<c\le1/4$, put $a=c/\sqrt d$; the models $P_0,\dots,P_d$ on $\{0,1\}^d$ have their first $j$ coordinates $\mathrm{Ber}(1/2+a)$ and the rest $\mathrm{Ber}(1/2-a)$, with $\Gamma(P_j)=\{0\}$ for $j\le\lfloor d/4\rfloor$, $\{1\}$ for $j\ge\lceil3d/4\rceil$, and $\{0,1\}$ otherwise.
--
--   There are absolute constants $C_1,C_2>0$ such that for all integers $d\ge1$, all $0<c\le1/4$, $0<\beta\le1/8$ and $0<\rho\le1/16$, the optimal weak-replication sample size satisfies
--   $$C_1F\le n^\star(\beta,\rho)\le C_2F,\qquad F=c^{-2}\Big[d\log\Big(1+\frac1{d\rho}\Big)+\log\frac1\beta\Big],$$
--   and a $(\beta,\rho)$-valid algorithm exists with
--   $$n=\Big\lceil\max\Big\{\frac d{2c^2}\log\Big(1+\frac{12}{d\rho}\Big),\ \frac6{c^2}\log\frac1\beta\Big\}\Big\rceil$$
--   samples.
--
--   The replication cost is resolved at two regimes, short-chain geometry when $d\rho\ge1$ and adjacent-position resolution when $d\rho<1$, while the confidence cost stays additive.
--
--   Differences from the source:
--   - encoding: n⋆(β, ρ) = Θ(c⁻²[d log(1 + 1/(dρ)) + log(1/β)]) with absolute (uniform) implicit constants → ∃ C₁ C₂ > 0, quantified before every parameter, with C₁·F ≤ N ≤ C₂·F for the least element N; reason: the Lean reading of Θ with constants independent of all displayed parameters
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
--   - encoding: Z = {0, 1}^d, models P_0, …, P_d → Fin d → Bool, models indexed by Fin (d + 1); coordinate i (0-based) has law Ber(1/2 + a) under P_j iff i < j; reason: Lean indexing; the same laws
--   - reading: "its data processing uses O(nd) integer arithmetic operations, followed by one shared random threshold comparison" → not formalized; reason: the sentence names no machine model, so it is an implementation remark rather than a statement about n⋆; the same decision as for the published Theorem 3.2
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 4.2, (4.6)–(4.7), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_Supplement_changePoint

namespace ReplicableDecisions.Supplement

/-- **Theorem 4.2 (Sharp sample size for early-versus-late change points).** Chen, *Replicable
Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 4.2, (4.6)–(4.7),
p.17 (PDF p.19). For the experiment (4.1), all integers `d ≥ 1`, `0 < c ≤ 1/4`, `0 < β ≤ 1/8` and
`0 < ρ ≤ 1/16`, `n⋆(β, ρ) = Θ(c⁻²[d log(1 + 1/(dρ)) + log(1/β)])`, the constants absolute and
uniform in all displayed parameters; more explicitly, a valid algorithm exists for
`n = ⌈max{(d/(2c²)) log(1 + 12/(dρ)), (6/c²) log(1/β)}⌉`.

**Formalization Note.** `N` is `n⋆` (`IsLeast`). The two constants are quantified before every
parameter. The theorem's last sentence (an `O(nd)` count of integer operations) names no machine
model and is not formalized. -/
theorem theorem_4_2 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc₀ : 0 < c) (hc : c ≤ 1 / 4) (β ρ : ℝ),
        0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
        let F : ℝ := (1 / c ^ 2) *
          ((d : ℝ) * Real.log (1 + 1 / ((d : ℝ) * ρ)) + Real.log (1 / β))
        let n₀ : ℕ := ⌈max ((d : ℝ) / (2 * c ^ 2) * Real.log (1 + 12 / ((d : ℝ) * ρ)))
          (6 / c ^ 2 * Real.log (1 / β))⌉₊
        ∃ N : ℕ, IsLeast (validSampleSizes (changePoint d c hd hc₀ hc) (earlyLateΓ d) β ρ) N ∧
          C₁ * F ≤ (N : ℝ) ∧ (N : ℝ) ≤ C₂ * F ∧
          n₀ ∈ validSampleSizes (changePoint d c hd hc₀ hc) (earlyLateΓ d) β ρ := by sorry

end ReplicableDecisions.Supplement
