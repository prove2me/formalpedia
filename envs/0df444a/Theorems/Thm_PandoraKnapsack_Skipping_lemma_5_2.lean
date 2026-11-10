-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_lemma_5_2
-- name    : PandoraKnapsack.Skipping.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:24:40.479832+00:00
-- url     : https://prove2.me/theorems/f127d984-290b-4bad-b5f0-c37cace8d839
-- title:
--   Lemma 5.2 — the time-indexed LP upper-bounds the fully-adaptive optimum
-- statement:
--   Let $I$ be a valid MPK instance on the grid $\{0,\dots,T+1\}$ with capacity $T$. Then $E[\mathrm{ADAPT}]\le\Psi(T)$: for every fully-adaptive policy $\pi$ there is a feasible solution $x$ of $\Psi(T)$ with
--   $$E[\mathrm{utility}(\pi)]\ \le\ \sum_{i,j}\sum_{t=0}^{T}w_{i,j,t}\,x_{i,j,t}.$$
--
--   Differences from the source:
--   - encoding: E[ADAPT] ≤ Ψ(T), an inequality between two optimal values → for every fully-adaptive policy π there is a feasible x of Ψ(T) with E[utility(π)] ≤ objective(x); reason: both maxima are attained (finitely many decision trees on the grid; a nonempty compact polytope), so the statements are equivalent; no real supremum is taken
--   - encoding: a fully-adaptive policy chooses the next pair as an arbitrary function of the realized history (Definition 2.3) → a deterministic function from the list of attempted (item, choice, realized size) triples to stop or a next pair; re-choosing an attempted item stops; expected utility by the exact recursion over the size laws; reason: this is the source's class; randomized policies are mixtures of these and do not raise the maximum
--   - encoding: LP variables x_{i,j,t} for t ∈ {0,…,b} → arrays Fin n → Fin m → ℕ → ℝ whose coordinates outside the index set are ignored; reason: same feasible points and objective values on the index set
--   - encoding: items [n] and choices [m] indexed from 1 → Fin n and Fin m, indexed from 0; reason: index shift; same instances
--   - reading: item-choice costs p_i^j paid up front (sign not stated) → 0 ≤ p_i^j in IsValid; reason: §2 calls p_i^j a cost incurred up front and Definition 2.1 divides by it; a negative cost would reward overflow, which the model never does
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Lemma 5.2, printed p. 22 (PDF 24)

import Definitions.Def_PandoraKnapsack_Skipping_Policies
import Definitions.Def_PandoraKnapsack_Skipping_TimeIndexedLP

namespace PandoraKnapsack.Skipping

/-- **Lemma 5.2** (Barak et al. 2026, *Pandora's Knapsack via Simple Policies*, supplied PDF,
SHA256 45e5830b…7a2d, printed p. 22, PDF 24). `E[ADAPT] ≤ Ψ(T)`, where `ADAPT` is the utility of
the optimal adaptive policy.

**Formalization Note.** `ADAPT(I)` is the maximum of `E[utility(π)]` over fully-adaptive
policies and `Ψ(T)` the maximum of the objective over the feasible set; the inequality is stated
as: for every fully-adaptive policy `π` there is a feasible solution of `Ψ(T)` whose objective is
at least `E[utility(π)]`. No supremum is taken. -/
theorem lemma_5_2 {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (π : AdaptivePolicy n m) :
    ∃ x : LPArray n m, PsiFeasible I T x ∧ adaptValue I π ≤ psiObjective I T x := by sorry

end PandoraKnapsack.Skipping
