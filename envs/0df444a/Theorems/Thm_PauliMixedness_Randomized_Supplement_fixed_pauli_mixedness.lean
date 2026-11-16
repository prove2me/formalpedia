-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_Supplement_fixed_pauli_mixedness
-- name    : PauliMixedness.Randomized.Supplement.fixed_pauli_mixedness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:58:53.751353+00:00
-- url     : https://prove2.me/theorems/f76be176-afc7-48dc-8eb3-7f90c500d6f0
-- title:
--   Theorem 1.5 — fixed Pauli mixedness testing, upper and lower bounds
-- statement:
--   The fixed-schedule Pauli copy complexity has both the following bounds. There is an absolute $C>0$ such that for every $N\ge0$, $\varepsilon>0$, and $0<\delta\le1$, there are a copy count $n$ and a protocol with one deterministic schedule of product Pauli basis measurements satisfying
--
--   $$n\le\left\lceil C\frac{(\sqrt{30})^N}{\varepsilon^2}\ln\frac1\delta\right\rceil.$$
--
--   Its acceptance probability on $\rho_{\rm mm}$ is at least $1-\delta$, and its rejection probability is at least $1-\delta$ on every complex density matrix $\rho$ at unhalved trace distance at least $\varepsilon$. All copies across all bases and amplification repetitions count toward $n$. The final outcome-only decision may use coins, but the schedule is a point mass.
--
--   There are also absolute $c>0$, $N_0\ge1$, $\varepsilon_0>0$ such that for all $N\ge N_0$ and $0<\varepsilon\le\varepsilon_0$, every such fixed-schedule protocol with worst-case success at least $2/3$ on both hypotheses satisfies
--
--   $$c(\sqrt{27})^N\le n\varepsilon^2.$$
--
--   Both clauses quantify over the same unrestricted complex state model. The lower bound covers arbitrary allocations of copies across bases and every randomized outcome-only decision. Together they distinguish the fixed-schedule regime from the randomized upper-bound goal.
--
--   Differences from the source:
--   - encoding: fixed/deterministic Pauli measurements → published PauliProtocol with schedule law a point mass and randomized outcome-only decision kernel; reason: the whole schedule is fixed before any copy is measured; only classical decision coins remain
--   - encoding: O and Ω copy bounds with confidence → absolute constants, integer ceiling in the upper bound, explicit asymptotic range and multiplied lower bound; reason: §4.1 p.15 gives √30 and confidence amplification, §5.3 p.22 gives √27; δ≥1/2 permits a zero-copy fair decision and δ=1 permits zero copies
--   - generalization: upper bound for an N-qubit system (N ≥ 1 implicit) → upper clause for every N : ℕ, including N = 0; reason: at N = 0 the only density matrix is ρ_mm, so for ε > 0 the alternative is empty and the zero-copy always-accept protocol succeeds; the instances N ≥ 1 are unchanged
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Theorem 1.5 p.3; upper proof §4.1 pp.13–15; lower proof §5.3 pp.21–22

import Definitions.Def_PauliMixedness_Randomized_Supplement_Fixed

namespace PauliMixedness.Randomized.Supplement

/-- Theorem 1.5 p.3, both clauses; proofs §4.1 pp.13-15 and §5.3 pp.21-22.
The schedule law is a point mass. n counts all bases and repetitions. -/
theorem fixed_pauli_mixedness :
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 →
        ∃ (n : ℕ) (A : PauliProtocol N n), IsFixed A ∧
          n ≤ ⌈C * Real.sqrt 30 ^ N / ε^2 * Real.log (1 / δ)⌉₊ ∧
          PauliSucceeds A ε δ) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ (n : ℕ) (A : PauliProtocol N n), IsFixed A →
          PauliSucceeds A ε (1 / 3) →
            c * Real.sqrt 27 ^ N ≤ (n : ℝ) * ε^2) := by sorry

end PauliMixedness.Randomized.Supplement
