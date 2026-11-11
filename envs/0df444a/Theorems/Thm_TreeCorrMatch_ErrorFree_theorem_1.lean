-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_theorem_1
-- name    : TreeCorrMatch.ErrorFree.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:27:07.905445+00:00
-- url     : https://prove2.me/theorems/27f930a3-a47e-4f15-88ff-087126be7956
-- title:
--   Theorem 1 — TBAlign: error-free almost-exact recovery above $\sqrt{C_{\mathrm{Otter}}}$, and exact recovery when $\lambda s\ge(1+\epsilon)\log n$
-- statement:
--   Let $s$ be a constant with $\sqrt{C_{\mathrm{Otter}}}<s\le1$, and let $\lambda=\lambda_n$ satisfy $\lambda_n\to\infty$ and $\lambda_n\le(\log n)^K$ for some $K$ and all large $n$. Let $(G,\tilde G)\sim\mathrm{CER}(n,\lambda_n,s)$ with planted permutation $\pi$, and run TBAlign with the parameters (1), where every call of the permanent approximator meets guarantee (15) and uses a fresh independent seed, and ApproxLR receives class-preserving ordered representatives of the local trees. Probabilities are over the graphs, $\pi$ and the seeds.
--
--   1. There is a deterministic sequence $\varepsilon_n\to0$ such that, with probability tending to $1$, **every** partial mapping $\pi'$ that TBAlign can output (for any edge orders in GreedyMatching and any choices in Step 3) satisfies both
--      - $\pi'$ contains no wrong match: $\pi'(u)=\pi(u)$ for every matched $u$;
--      - almost all nodes are matched:
--
--   $$\big|\{u\in[n]: u\text{ is matched under }\pi'\}\big|\ \ge\ n(1-\varepsilon_n).$$
--
--   2. If moreover $\lambda_n s\ge(1+\epsilon)\log n$ for a constant $\epsilon>0$ and all large $n$, then with probability tending to $1$ TBAlign has at least one complete output, and every complete mapping $\hat\pi$ that TBAlign can output equals $\pi$.
--
--   This is the main recovery guarantee of the paper: above Otter's threshold, a likelihood-ratio method on local trees with approximated permanents yields a partial matching of size $n-o(n)$ without a single error, and, in the exact-recovery regime, the seeded completion recovers $\pi$ entirely.
--
--   **Formalization Note** "With probability $1-o(1)$" is a limit $\to1$; the $o(1)$ of (6) is one sequence $\varepsilon_n\to0$ fixed before the probability, so both clauses of item 1 hold in one event. The approximator is a hypothesis object (`IsPermApprox`), and the class-preserving map $r$ is quantified outside the probability.
--
--   Differences from the source:
--   - generalization: the FPRAS ApproxPer of [40] (Lemma 3, Remark 1) → every approximator App with seed law μ₀ that, for each entrywise nonnegative square matrix A and δ, η ∈ (0, 1/2), is measurable in the seed, nonnegative and meets guarantee (15); every call gets its own independent seed; reason: the paper uses only (15), nonnegativity and the fresh independent bits of Remark 1; the FPRAS of [40] is one such approximator, so the statement specializes to the paper's
--   - reading: ApproxLR receives the unlabeled pair ([T], [T̃]) and enumerates children in an unspecified order → ApproxLR acts on ordered trees; the test is applied to r(h), r(h̃) for an arbitrary fixed map r on ordered trees with [r(h)] = [h]; reason: the enumeration is left open by the paper; quantifying over every class-preserving r covers every rule (a canonical representative, or the order by vertex index)
--   - reading: the arbitrary edge order of GreedyMatching, the arbitrary choice in Step 3 and the arbitrary tie-breaking in Step 4 → the events hold for every possible output of TBAlign (IsTBPartial, IsTBOutput are relations over all choices); reason: the algorithm leaves the choices arbitrary; the paper's proof holds for every choice
--   - encoding: π̂ = π, where Step 4 can run only while an unmatched pair (u, ṽ) exists (so π̂ exists only for an injective π′) → the exact-recovery event asserts that some complete output (π′, π̂) exists and that every complete output has π̂ = π; reason: the paper's event presupposes that π̂ is produced; without the existence clause the event would hold vacuously on outcomes where no completion exists
--   - encoding: 'with probability 1 − o(1)' and the o(1) of (6) → Tendsto (probability) atTop (𝓝 1), with one deterministic ε_n → 0 chosen before the probability, both clauses of item 1 in one event; reason: standard reading; keeping the clauses in one event rules out the empty π′
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: λs ≥ (1 + ϵ) log n for some constant ϵ > 0 → ∃ ϵ > 0 with (1 + ϵ) log n ≤ λ_n s for all large n; reason: only large n matter for a limit
--   - encoding: CER(n, λ, s) with parent edge probability λ/(ns), λ ∈ (0, ns] → parent edge probability clamped to [0, 1]; reason: the clamp changes only the finitely many n with λ_n > ns and no limit
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
--   - encoding: node set [n], partial mapping π′ : V′ → Ṽ, complete mapping π̂ : V → Ṽ → Fin n; maps Fin n → Option (Fin n) (none = unmatched), π′ as Step 3 builds it, π̂ defined on every node; reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), pp. 7–8, Theorem 1 (PDF pp. 9–10); restated p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_CER
import Definitions.Def_TreeCorrMatch_ErrorFree_TBAlign

open Filter Topology MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem theorem_1 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀]
    (App : PermApprox Ω₀) (hApp : IsPermApprox μ₀ App) (r : OTree → OTree)
    (hr : ∀ t, cls (r t) = cls t) :
    (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => cerSeedProb n (lam n) s (tbSeedLaw μ₀ n) (fun x ω =>
        ∀ π' : Fin n → Option (Fin n),
          IsTBPartial App r (lam n) s (tauParam n (lam n) : ℕ∞) x.1 x.2.1 ω π' →
            (∀ u v, π' u = some v → v = x.2.2 u) ∧
            (n : ℝ) * (1 - ε n) ≤ ((Finset.univ.filter fun u => π' u ≠ none).card : ℝ)))
        atTop (𝓝 1)) ∧
    ((∃ ϵ : ℝ, 0 < ϵ ∧ ∀ᶠ n : ℕ in atTop, (1 + ϵ) * Real.log n ≤ lam n * s) →
      Tendsto (fun n : ℕ => cerSeedProb n (lam n) s (tbSeedLaw μ₀ n) (fun x ω =>
        (∃ π' πc : Fin n → Option (Fin n),
          IsTBOutput App r (lam n) s (tauParam n (lam n) : ℕ∞) x.1 x.2.1 ω π' πc) ∧
        ∀ π' πc : Fin n → Option (Fin n),
          IsTBOutput App r (lam n) s (tauParam n (lam n) : ℕ∞) x.1 x.2.1 ω π' πc →
            ∀ u, πc u = some (x.2.2 u)))
        atTop (𝓝 1)) := by sorry

end TreeCorrMatch.ErrorFree
