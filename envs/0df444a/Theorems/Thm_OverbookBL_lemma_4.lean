-- Prove2me | Theorems.Thm_OverbookBL_lemma_4
-- name    : OverbookBL.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:10.038391+00:00
-- url     : https://prove2.me/theorems/2dac0b65-2d43-40d6-93db-55e8e136f213
-- title:
--   Lemma 4 — exchanging $R_{ij}/p_j$ type-$j$ for $R_{ij}/p_i$ type-$i$ customers (corrected: $-V_B$ in (1); $\ge$, strict if $q_i>q_j$)
-- statement:
--   For every pair of types $i<j$ there is a constant $R_{ij}\in\mathbb Z^+$ with $R_{ij}/p_i$ and $R_{ij}/p_j$ integers such that, for every capacity $B$, past accepted arrivals $\vec x[t-1]$ and vector $\vec x^\star$,
--
--   $$
--   \text{obj}\Big(\vec x^\star+\frac{R_{ij}}{p_i}e_i\Big)\ \ge\ \text{obj}\Big(\vec x^\star+\frac{R_{ij}}{p_j}e_j\Big),
--   $$
--
--   with strict inequality when $q_i>q_j$; here obj is the objective of problem (1) with past $\vec x[t-1]$.
--
--   Both vectors add customers with the same expected number $R_{ij}$ of show-ups; the higher critical ratio, or for equal ratios the smaller variance, of type $i$ makes the exchange favourable. Lemma 5 derives from it that optima are close to index solutions.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - correction: the objective of x⃗⋆ + (Rᵢⱼ/pᵢ)eᵢ "is always greater" → ≥ always, > when qᵢ > qⱼ; reason: false when qᵢ = qⱼ: k = 2, (v, p) = (1/2, 1), (1/4, 1/2), no past, x⋆ = 0, B > 2R gives equal objectives R/2 for every R
--   - generalization: for feasible solutions x⃗⋆ + (Rᵢⱼ/p)e of (1) with N[t, T] → for every vector x⋆, no caps; reason: feasibility plays no role in the comparison; specializes to feasible vectors
--   - encoding: Rᵢⱼ with Rᵢⱼ/pᵢ, Rᵢⱼ/pⱼ integers (p.19) → R, nᵢ, nⱼ ∈ ℕ with 1 ≤ R, nᵢpᵢ = R, nⱼpⱼ = R; reason: same constants
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 4, p.19 (proof pp.19–20 and Appendix A.3, pp.43–45)

import Definitions.Def_OverbookBL_obj

namespace OverbookBL

/-- **Lemma 4** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.19), with
the corrected conclusion. For every pair of types `i < j` there is a constant `Rᵢⱼ ∈ ℤ⁺` with
`Rᵢⱼ/pᵢ` and `Rᵢⱼ/pⱼ` integers such that, for every capacity `B`, past accepted arrivals
`x⃗[t−1]` and solution `x⋆`, the objective of problem (1) at `x⋆ + (Rᵢⱼ/pᵢ) eᵢ` is at least its
objective at `x⋆ + (Rᵢⱼ/pⱼ) eⱼ`, and strictly greater when `qᵢ > qⱼ`.

**Formalization Note** `nᵢ = Rᵢⱼ/pᵢ` and `nⱼ = Rᵢⱼ/pⱼ` are the natural numbers with
`nᵢ pᵢ = nⱼ pⱼ = Rᵢⱼ`. The paper says "always greater"; that is false when `qᵢ = qⱼ`
(k = 2, `(v, p) = (1/2, 1), (1/4, 1/2)`, past `0`, `x⋆ = 0`, `B > 2R`: both objectives equal
`R/2` for every admissible `R`), so the strict inequality is kept only for `qᵢ > qⱼ`. Problem (1)
is read with `−V_B`. The two vectors are not required to be feasible for any cap: feasibility
plays no role in the comparison. -/
theorem lemma_4 {k : ℕ} (I : Instance k) (i j : Fin k) (hij : i < j) : ∃ R nᵢ nⱼ : ℕ, 1 ≤ R ∧ (nᵢ : ℝ) * I.p i = R ∧ (nⱼ : ℝ) * I.p j = R ∧ ∀ (B : ℕ) (past x : Fin k → ℕ), obj I B past (x + nⱼ • Pi.single j 1) ≤ obj I B past (x + nᵢ • Pi.single i 1) ∧ (I.v j / I.p j < I.v i / I.p i → obj I B past (x + nⱼ • Pi.single j 1) < obj I B past (x + nᵢ • Pi.single i 1)) := by sorry

end OverbookBL
