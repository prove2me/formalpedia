-- Prove2me | Theorems.Thm_OverbookBL_lemma_6
-- name    : OverbookBL.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:44.715252+00:00
-- url     : https://prove2.me/theorems/b4357215-ba6d-4109-b816-bb855e327836
-- title:
--   Lemma 6 — global optimum vs. admissible index solution (corrected: $-V_B$ in (1); (ii) assumes local optimality above the threshold)
-- statement:
--   Let $\delta\ge1$ have the local Lipschitz property of Lemma 2. Consider problem (1) with capacity $B$, past accepted arrivals $\vec x[t-1]$ and future arrivals $\vec N$ with $N_j>0$ for all $j$ (footnote 4). Let $\vec x^\star$ be a globally optimal solution that is locally optimal for every type, and $\vec x'$ an optimal index solution that is locally optimal at its threshold index $\tilde\jmath$. Then
--
--   1. $\displaystyle\sum_j(x'_j-x^\star_j)^+\le k\delta\Big[1+\sum_j(x^\star_j-x'_j)^+\Big]$;
--   2. if moreover $\vec x'$ is locally optimal at every $j>\tilde\jmath$, then $\displaystyle\sum_j(x^\star_j-x'_j)^+\le k\delta\sum_j(x'_j-x^\star_j)^+$.
--
--   The two parts bound the distance between a global optimum and an index optimum, which gives the constant of Theorem 1.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - correction: (ii) for every such x⃗′ → (ii) assumes in addition that x⃗′ is locally optimal at every j > j̃; reason: the proof (pp.21–22, A.4) asserts this property but it fails under ties, and (ii) is then false: k = 2, (v, p) = (1/4, 1/2), (1/8, 1/4), B = 1, no past, N = (1, 1), x⃗′ = (1, 0), x⃗⋆ = (1, 1) satisfy every hypothesis and (ii) reads 1 ≤ 0 (checked in Lean)
--   - generalization: δ as constructed in Lemma 2 → every δ ≥ 1 with the property of Lemma 2 (IsLipConst); reason: the constructed δ has the property; the proof uses nothing else about it
--   - encoding: problem (1) "with arrivals N⃗" → arbitrary past acceptance vector and future arrival vector N; reason: problem (1) always carries a past vector; footnote 4's Nⱼ > 0 is kept as a hypothesis
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 6, p.21 (proofs pp.21–24 and Appendix A.4, p.45)

import Definitions.Def_OverbookBL_IsAdmissible
import Definitions.Def_OverbookBL_IsLipConst

namespace OverbookBL

/-- **Lemma 6** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.21), with
part (ii) corrected. Let `δ ≥ 1` be a constant as constructed in Lemma 2. Consider problem (1)
with future arrivals `N⃗` (with `Nⱼ > 0` for every `j`, footnote 4) and past accepted arrivals
`x⃗[t−1]`, an optimal solution `x⋆` that is locally optimal for every type `j`, and an optimal index
solution `x′` that is locally optimal at its threshold index `j̃`. Then
(i) `∑ⱼ (x′ⱼ − x⋆ⱼ)⁺ ≤ kδ [1 + ∑ⱼ (x⋆ⱼ − x′ⱼ)⁺]`;
(ii) if moreover `x′` is locally optimal at every `j > j̃`, then
`∑ⱼ (x⋆ⱼ − x′ⱼ)⁺ ≤ kδ ∑ⱼ (x′ⱼ − x⋆ⱼ)⁺`.

**Formalization Note** "`δ` as constructed in Lemma 2" is any `δ ≥ 1` with the property of
Lemma 2 (`IsLipConst`). The hypothesis of (ii) is added: the proof (p.22, A.4) asserts that `x′`
is locally optimal at every `j > j̃`, but that step fails under ties, and (ii) is then false:
`k = 2`, `(v, p) = (1/4, 1/2), (1/8, 1/4)`, `B = 1`, no past, `N = (1, 1)`, `x′ = (1, 0)`,
`x⋆ = (1, 1)` satisfy every hypothesis, and (ii) reads `1 ≤ 0`. Problem (1) is read with `−V_B`;
optimality of `x⋆` is global over `0 ≤ x ≤ N`, optimality of `x′` is among index solutions. -/
theorem lemma_6 {k : ℕ} (I : Instance k) (δ : ℕ) (hδ : 1 ≤ δ) (hδL : IsLipConst I δ) (B : ℕ) (past N : Fin k → ℕ) (hN : ∀ j, 0 < N j) (xs x' : Fin k → ℕ) (e : Fin k) (hxs : IsGlobOpt I B past N xs) (hxsloc : ∀ j, IsLocOpt I B past N xs j) (hx' : IsOptIndex I B past N x') (he : IsThreshold N x' e) (hx'loc : IsLocOpt I B past N x' e) : (∑ j, max ((x' j : ℝ) - xs j) 0 ≤ k * δ * (1 + ∑ j, max ((xs j : ℝ) - x' j) 0)) ∧ ((∀ j, e < j → IsLocOpt I B past N x' j) → ∑ j, max ((xs j : ℝ) - x' j) 0 ≤ k * δ * ∑ j, max ((x' j : ℝ) - xs j) 0) := by sorry

end OverbookBL
