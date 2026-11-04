-- Prove2me | Theorems.Thm_OverbookBL_lemma_5
-- name    : OverbookBL.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:02.400595+00:00
-- url     : https://prove2.me/theorems/72bae65c-4228-477a-85f8-10109494d271
-- title:
--   Lemma 5 — every optimum nearly fills type $i$ or nearly empties type $j$ ($i<j$) (corrected: $-V_B$ in (1))
-- statement:
--   For every pair of types $i<j$ there is a constant $R_{ij}$, depending only on the instance, such that for every capacity $B$, past accepted arrivals $\vec x[t-1]$ and future arrivals $N[t,T]$, every optimal solution $\vec x^\star$ of problem (1) satisfies at least one of
--
--   1. $x^\star_i>N_i[t,T]-R_{ij}/p_i$;
--   2. $x^\star_j<R_{ij}/p_j$.
--
--   An optimum cannot leave many higher-ratio customers unaccepted while accepting many lower-ratio ones; up to constants it has the shape of an index solution. Theorem 1 combines this with Lemma 6.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: x⋆ᵢ > N[t, T] − Rᵢⱼ/pᵢ → (Nᵢ : ℝ) − R/pᵢ < x⋆ᵢ; reason: the printed N[t, T] is the type-i count (subscript dropped); real arithmetic
--   - reading: "for every i and j with i < j there exists a constant Rᵢⱼ" after fixing x⃗⋆ → ∃ R before B, the past, N and x⋆; reason: Theorem 1's proof needs Rᵢⱼ independent of B, T and A⃗ (p.26); a constant depending on x⃗⋆ makes the lemma empty
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 5, pp.20–21

import Definitions.Def_OverbookBL_IsAdmissible

namespace OverbookBL

/-- **Lemma 5** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, pp.20–21).
For every pair of types `i < j` there exists a constant `Rᵢⱼ` such that every optimal solution `x⋆`
of problem (1) with future arrivals `N[t, T]` and past accepted arrivals `x⃗[t−1]` satisfies at
least one of
(i) `x⋆ᵢ > Nᵢ[t, T] − Rᵢⱼ/pᵢ`;
(ii) `x⋆ⱼ < Rᵢⱼ/pⱼ`.

**Formalization Note** `Rᵢⱼ` is chosen before the capacity, the past, the future arrivals and the
solution (the reading the proof of Theorem 1 needs: "independent of `B`, `T` and `A⃗`", p.26). The
printed "`N[t, T]`" in (i) is the type-`i` count `Nᵢ[t, T]`. Comparisons are in `ℝ`. "Optimal" is
global optimality over `0 ≤ x ≤ N`. Problem (1) is read with `−V_B`. -/
theorem lemma_5 {k : ℕ} (I : Instance k) (i j : Fin k) (hij : i < j) : ∃ R : ℝ, ∀ (B : ℕ) (past N x : Fin k → ℕ), IsGlobOpt I B past N x → ((N i : ℝ) - R / I.p i < x i ∨ (x j : ℝ) < R / I.p j) := by sorry

end OverbookBL
