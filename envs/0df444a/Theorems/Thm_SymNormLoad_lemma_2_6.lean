-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_6
-- name    : SymNormLoad.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:41.207247+00:00
-- url     : https://prove2.me/theorems/e69caa44-d6f4-4b5e-a99e-a4b4e1bc710f
-- title:
--   Lemma 2.6 — greedy telescoping comparison $\Phi(L)-M\le\Phi(L+z)-\Phi(L)$
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $h$ the load transform, $g=e^h$ and $\Phi(x)=\sum_i g(x_i)$. Let $p_1,\dots,p_N\in\mathbb R^M_{\ge0}$ be the jobs, let $L$ be the final load vector produced by Algorithm 2.4 on them, and let $z$ be the load vector of any fixed integral offline assignment of the same jobs. Then
--   $$
--   \Phi(L)-M\ \le\ \Phi(L+z)-\Phi(L).\tag{2.6}
--   $$
--
--   The left side is the potential increase caused by the algorithm's assignments, the right side the increase from adding the offline loads on top of the algorithm's final loads.
--
--   Differences from the source:
--   - generalization: "normalized" load vectors L and z, i.e. the instance scaled so that OPT = 1 (Simplifying Assumption, p.9) → every instance p ≥ 0 as given, with no hypothesis on OPT or on Ψ(z); reason: the proof (p.12) uses only greediness and convexity of g, never the scale; on a normalized instance the Lean statement is exactly (2.6)
--   - encoding: the final load vector L of Algorithm 2.4 (ties to the smallest index) → greedyLoad h p: the loads after running the step of (2.4) on jobs 0, …, N−1, ties to the least element of Fin M; reason: the same algorithm, 0-based indices
--   - encoding: jobs 1, …, N with processing times p_{ji} ≥ 0 → jobs Fin N (0-based), p : Fin N → Fin M → ℝ with ∀ j i, 0 ≤ p j i; reason: relabelling; the same instances
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.6, Eq. (2.6), p.11

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform
import Definitions.Def_SymNormLoad_loadVec
import Definitions.Def_SymNormLoad_Phi__cbe170
import Definitions.Def_SymNormLoad_greedyLoad

namespace SymNormLoad

/-- **Lemma 2.6 (greedy telescoping comparison, (2.6)).** Chen–Im–Sirri, *Online Load Balancing
under Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.6, p.11. Let `L` be the final
normalized load vector produced by Algorithm 2.4, and let `z` be the normalized load vector of any
fixed integral offline assignment of the same jobs. Then `Φ(L) − M ≤ Φ(L + z) − Φ(L)`.

**Formalization Note** The "normalized instance" is `p` itself; the lemma has no norm hypothesis.
Jobs `Fin N`, machines `Fin M`, processing times `p j i ≥ 0` (zeros allowed). `L` is
`greedyLoad h p` (smallest-index ties) and `z = loadVec p σ`. `2 ≤ M` is the standing assumption
of §1.1. -/
theorem lemma_2_6 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h)
    (N : ℕ) (p : Fin N → Fin M → ℝ) (hp : ∀ j i, 0 ≤ p j i) (σ : Fin N → Fin M) :
    Phi h (greedyLoad h p) - M ≤
      Phi h (greedyLoad h p + loadVec p σ) - Phi h (greedyLoad h p) := by sorry

end SymNormLoad
