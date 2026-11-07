-- Prove2me | Theorems.Thm_TFNPRom_fact_2
-- name    : TFNPRom.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:11.617948+00:00
-- url     : https://prove2.me/theorems/6773d4f2-7fda-43e1-9f2f-474208e79b03
-- title:
--   Fact 2 — list recovery of folded Reed-Solomon codes (corrected: $1\le s$)
-- statement:
--   Let $F$ be a finite field, $\gamma$ a generator of $F^*$, $n=|F|-1$, and suppose $m$ divides $n$. Let $\alpha,\beta$ be positive integers, $d\in\mathbb N$, $1\le s\le m$, and $\delta\in(0,1)$. If
--   $$
--   \frac{(1-\delta)n}{m}\ \ge\ \Big(1+\frac s\beta\Big)\cdot\frac{(n\alpha d^s)^{1/(s+1)}}{m-s+1}
--   \qquad\text{and}\qquad
--   (\beta+s)\Big(\frac{n\alpha}{d}\Big)^{1/(s+1)}<|F|,
--   $$
--   then $\mathrm{FoldedRS}^m_{F,\gamma,d}$ is $(\delta,\alpha,|F|^s)$-list recoverable.
--
--   This is the external coding-theoretic input of the construction, cited by the paper from Yamakawa–Zhandry and Rudra's thesis, and the source of the well-spreadness of the hard hypergraph.
--
--   **Formalization Note** At $d=0$ the paper's $n\alpha/d$ is undefined and Lean's division gives $0$; the conclusion still holds there, since the code has $|F|\le|F|^s$ words.
--
--   Differences from the source:
--   - correction: "s ≤ m" with s = 0 allowed → 1 ≤ s ≤ m; reason: false at s = 0: F = F_5, γ = 2, n = 4, m = 1, d = 3, α = β = 1, δ = 1/2 satisfies both inequalities, and the code is all of F^4, so at least two words agree with S_i = {0} on ≥ 2 of 4 coordinates against the claimed bound |F|^0 = 1 (proved in the verification file)
--   - reading: $S_i\subset\Gamma$ in list recovery → $S_i\subseteq\Gamma$; reason: the larger class makes the definition the stronger one, and Claim 11 needs it
--   - encoding: nα/d undefined at d = 0 → Lean division, value 0; reason: the conclusion holds at d = 0 as well, so the value only decides whether the case is covered, and it is covered truthfully
--   - encoding: 1-based indices γ^{i-1} → 0-based indices γ^i; reason: same code
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…), Fact 2, p.18 (restating [YZ24, Lemma 4.3], [Rud07, §3.6])

import Mathlib
import Definitions.Def_TFNPRom_foldedRS
import Definitions.Def_TFNPRom_IsListRecoverable

namespace TFNPRom

/-- **Fact 2** (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), p.18; restatement of [YZ24, Lemma 4.3], originally [Rud07, §3.6]). Let `F` be a finite
field with generator `γ`, `n = |F| - 1`, `m ∣ n`, `α, β` positive integers, `1 ≤ s ≤ m` and `δ ∈ (0,1)`. If
`(1 - δ) n / m ≥ (1 + s/β) (n α d^s)^{1/(s+1)} / (m - s + 1)` and `(β + s) (n α / d)^{1/(s+1)} < |F|`, then
`FoldedRS^m_{F,γ,d}` is `(δ, α, |F|^s)`-list recoverable.

**Formalization Note** The hypothesis `1 ≤ s` corrects the printed "`s ≤ m`": at `s = 0` the statement is
false (`F = F_5`, `γ = 2`, `m = 1`, `d = 3`, `α = β = 1`, `δ = 1/2`). At `d = 0` the paper's `n α / d` is
undefined and Lean's value `0` makes the second inequality hold; the conclusion holds there since the
code has `|F| ≤ |F|^s` words. -/
theorem fact_2 {F : Type} [Field F] [Fintype F] [DecidableEq F] (γ : F)
    (hγ : orderOf γ = Fintype.card F - 1) (m d s α β : ℕ) (δ : ℝ)
    (hm : m ∣ Fintype.card F - 1) (hα : 0 < α) (hβ : 0 < β) (hs₁ : 1 ≤ s) (hs : s ≤ m)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (h₁ : (1 + (s : ℝ) / β) *
        (((Fintype.card F - 1 : ℕ) : ℝ) * α * (d : ℝ) ^ s) ^ ((1 : ℝ) / ((s : ℝ) + 1)) /
          ((m : ℝ) - s + 1) ≤ (1 - δ) * ((Fintype.card F - 1 : ℕ) : ℝ) / m)
    (h₂ : ((β : ℝ) + s) * (((Fintype.card F - 1 : ℕ) : ℝ) * α / d) ^ ((1 : ℝ) / ((s : ℝ) + 1)) <
      (Fintype.card F : ℝ)) :
    IsListRecoverable (foldedRS γ m d) δ α (Fintype.card F ^ s) := by sorry

end TFNPRom
