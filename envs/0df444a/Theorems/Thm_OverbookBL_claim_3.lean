-- Prove2me | Theorems.Thm_OverbookBL_claim_3
-- name    : OverbookBL.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:00.768127+00:00
-- url     : https://prove2.me/theorems/01add5a2-f1d7-46e0-adde-7fb0267415ed
-- title:
--   Claim 3 — $x'_i-x^\star_i\le\delta\sum_{j<i}(x^\star_j-x'_j)^+$ (corrected: $-V_B$ in (1); $x^\star$ locally optimal at $i$)
-- statement:
--   Let $\delta\ge1$ have the local Lipschitz property of Lemma 2 and fix a type $i$. Let $\vec x^\star$ be an optimal index solution of problem (1) with past accepted arrivals $\vec x[t-2]$ and exact future arrivals $N[t-1,T]$ (the clairvoyant index solution), and let $\vec x'$ be an optimal index solution of (1) with the same past and the estimate $\widetilde N^f[t-1]$, locally optimal at its threshold index (the solution found by Algorithm 1). Suppose $x'_i\ge\widetilde N^f_i[t-1]/2$, $x^\star_i=0$, $N_i[t-1,T]\ge1$, and that $\vec x^\star$ is locally optimal at $i$. Then
--
--   $$
--   x'_i-x^\star_i\le\delta\sum_{j=1}^{i-1}\big(x^\star_j-x'_j\big)^+ .
--   $$
--
--   When the online policy accepts a type-$i$ customer that the clairvoyant index solution rejects, the online solution is above the clairvoyant one in type $i$ by at most $\delta$ times its deficit in the better types. Lemma 3 turns this into a bound on the probability of a loss in each period.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - correction: x⃗′, x⃗⋆ "as described" (p.26) → adds the hypothesis that x⃗⋆ is locally optimal at i; reason: the proof (p.46) takes this from the proof of Lemma 6, a step that fails under ties; without it the claim is false: k = 2, (v, p) = (1/4, 1/2), (1/8, 1/4), B = 1, no past, N = Ñ = (1, 1), i = 2, x⃗⋆ = (1, 0), x⃗′ = (1, 1) give 1 ≤ 0 (checked in Lean); this arises in a run with T = 2
--   - generalization: the configuration of a run of Algorithm 1 in period t − 1 (§4.3) → arbitrary past, N and Ñ; reason: specializes to the vectors of a run
--   - reading: x⃗′ is "the solution found by Algorithm 1 in period t − 1" (p.26), from line 6, "Find optimal index solution x⃗′" → x⃗′ an optimal index solution locally optimal at its threshold index (IsAdmissible); reason: p.21 states that this is the only property assumed of the solution of line 6
--   - generalization: δ as constructed in Lemma 2 → every δ ≥ 1 with the property of Lemma 2 (IsLipConst); reason: the constructed δ has the property
--   - encoding: δ[Σ_{j=1}^{i−1} (x⋆ⱼ − x′ⱼ)+] (unbalanced bracket) → δ · Σ_{j<i} max(x⋆ⱼ − x′ⱼ, 0) in ℝ; reason: the evident reading
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Claim 3, p.26 (proof Appendix A.5, pp.46–47)

import Definitions.Def_OverbookBL_IsAdmissible
import Definitions.Def_OverbookBL_IsLipConst

namespace OverbookBL

/-- **Claim 3** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.26; proof
in Appendix A.5, pp.46–47), stated for the configuration of §4.3 with one added hypothesis. Let
`δ ≥ 1` be as constructed in Lemma 2 and fix a type `i`. Let `x⋆` be an optimal index solution of
problem (1) with past accepted arrivals `past = x⃗[t−2]` and exact future arrivals `N = N[t−1, T]`
(the clairvoyant index solution), and `x′` an optimal index solution of (1) with the same past and
the estimate `Ñf = Ñᶠ[t−1]`, locally optimal at its threshold index (the solution found by
Algorithm 1, p.21). Suppose
`x′ᵢ ≥ Ñᶠᵢ[t−1]/2`, `x⋆ᵢ = 0`, `Nᵢ[t−1, T] ≥ 1`, and that `x⋆` is locally optimal at `i`. Then
`x′ᵢ − x⋆ᵢ ≤ δ ∑_{j<i} (x⋆ⱼ − x′ⱼ)⁺`.

**Formalization Note** The configuration is stated for arbitrary `past`, `N`, `Ñf` rather than
those produced by a run of Algorithm 1. The hypothesis "`x⋆` locally optimal at `i`" is added: the
proof (p.46) takes it "from the proof of Lemma 6", a step that fails under ties, and without it the
claim is false: `k = 2`, `(v, p) = (1/4, 1/2), (1/8, 1/4)`, `B = 1`, no past, `N = Ñf = (1, 1)`,
`i = 2`, `x⋆ = (1, 0)`, `x′ = (1, 1)` satisfy the printed hypotheses and give `1 ≤ 0`. This
configuration arises in a run with `T = 2`, `A⃗ = (2, 1)`, `A⃗′ = (·, 1)`. As on p.26, `x⋆` is only
assumed to be an optimal index solution (`IsOptIndex`). The printed bracket is
unbalanced; the sum is `∑_{j=1}^{i−1} (x⋆ⱼ − x′ⱼ)⁺`. Problem (1) is read with `−V_B`. -/
theorem claim_3 {k : ℕ} (I : Instance k) (δ : ℕ) (hδ : 1 ≤ δ) (hδL : IsLipConst I δ) (B : ℕ) (past N Nf : Fin k → ℕ) (i : Fin k) (xs x' : Fin k → ℕ) (hxs : IsOptIndex I B past N xs) (hx' : IsAdmissible I B past Nf x') (hxsi : xs i = 0) (hNi : 1 ≤ N i) (hx'i : (Nf i : ℝ) / 2 ≤ x' i) (hxsloc : IsLocOpt I B past N xs i) : (x' i : ℝ) - xs i ≤ δ * ∑ j ∈ Finset.univ.filter (fun j => j < i), max ((xs j : ℝ) - x' j) 0 := by sorry

end OverbookBL
