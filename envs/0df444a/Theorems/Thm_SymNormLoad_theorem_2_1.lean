-- Prove2me | Theorems.Thm_SymNormLoad_theorem_2_1
-- name    : SymNormLoad.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:51.918214+00:00
-- url     : https://prove2.me/theorems/0ce34de5-3e3c-474a-ace0-b26b008babd6
-- title:
--   Theorem 2.1 — a deterministic $20\ln(2M)$-competitive online algorithm for every monotone symmetric norm on $M$ unrelated machines
-- statement:
--   Let $M\ge2$ and let $\Psi$ be a monotone symmetric norm on $\mathbb R^M$. Then there is a deterministic online algorithm $A$ for scheduling on $M$ unrelated machines such that, for every finite sequence of jobs with processing-time vectors $p_1,\dots,p_N\in\mathbb R^M_{\ge0}$ and every integral offline assignment $\sigma$ of these jobs,
--   $$
--   \Psi(L_A)\ \le\ 20\ln(2M)\cdot\Psi(L_\sigma),
--   $$
--   where $L_A$ is the load vector produced by $A$ and $L_\sigma$ that of $\sigma$. The algorithm knows $\Psi$ and $M$ in advance but not the jobs to come, their number, or the optimum; each job is assigned integrally and irrevocably on arrival.
--
--   This is an $O(\log M)$ competitive ratio for every symmetric norm, improving the previous $O(\log^2M)$ bound and matching the $\Omega(\log M)$ lower bound for makespan.
--
--   Differences from the source:
--   - encoding: 20 ln(2M)-competitive: ALG ≤ 20 ln(2M) · OPT on every input (footnote 1) → IsCompetitive Ψ A (20 * Real.log (2 * M)): Ψ(L_A) ≤ 20 ln(2M) · Ψ(L_σ) for every N, every p ≥ 0 and every σ; reason: OPT is the minimum over the finitely many σ
--   - encoding: a deterministic online algorithm → A : OnlineAlgorithm M, a rule from the prefix p_0, …, p_j to the machine of job j; reason: the rule sees neither later jobs nor N; same class of algorithms
--   - encoding: jobs 1, …, N with processing times p_{ji} ≥ 0 → jobs Fin N (0-based), p : Fin N → Fin M → ℝ with ∀ j i, 0 ≤ p j i; reason: relabelling; the same instances
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Theorem 2.1, p.8 (proof completed in App. A.2, pp.38–39)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_OnlineAlgorithm
import Definitions.Def_SymNormLoad_IsCompetitive

namespace SymNormLoad

/-- **Theorem 2.1.** Chen–Im–Sirri, *Online Load Balancing under Symmetric Norms*, manuscript
(STOC 2027 submission), Theorem 2.1, p.8 (proof completed in App. A.2, pp.38–39). For every
monotone symmetric norm `Ψ`, there is a deterministic online algorithm on `M` unrelated machines
that is `20 ln(2M)`-competitive.

**Formalization Note** `M ≥ 2` is the standing assumption of §1.1. The algorithm is chosen after
`M` and `Ψ` (the norm is known in advance) and before the input; it sees only the prefix of jobs
so far (`OnlineAlgorithm`). Competitiveness is against every integral offline assignment, on
every finite job sequence with processing times in `ℝ^M_{≥0}` (zeros allowed), with no additive
constant (`IsCompetitive`). OPT is neither known nor assumed positive. -/
theorem theorem_2_1 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) :
    ∃ A : OnlineAlgorithm M, IsCompetitive Ψ A (20 * Real.log (2 * M)) := by sorry

end SymNormLoad
