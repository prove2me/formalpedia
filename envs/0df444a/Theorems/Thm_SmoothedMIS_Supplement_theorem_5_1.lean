-- Prove2me | Theorems.Thm_SmoothedMIS_Supplement_theorem_5_1
-- name    : SmoothedMIS.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:39:08.926212+00:00
-- url     : https://prove2.me/theorems/96af3e60-8666-4b6a-ab94-dc00b5bcd875
-- title:
--   Theorem 5.1 — with addition-only smoothing $p\le(\frac12-\delta)\ln n/n$, MIS with probability $\ge\sigma$ needs $\Omega(\log n/\log\log n)$ LOCAL rounds
-- statement:
--   This is **Theorem 5.1**, a lower bound from §5: smoothing with a parameter below $\tfrac12\ln n/n$ gives no advantage over worst-case graphs.
--
--   Here $\ln$ is the natural logarithm. The **smoothing** draws independent coins $\omega_e\in\{0,1\}$, one per pair $e$ of vertices of $[n]$, each equal to $1$ with probability $p(n)$. Every node also has a private infinite tape of fair coins, independent of the smoothing. The probability below is over the smoothing and the tapes jointly.
--
--   A **$T$-round randomized LOCAL algorithm with full information** on $n$ nodes is a rule that gives each node $v$ an output bit as a function of its **radius-$T$ view**. The view consists of the vertices at distance at most $T$ from $v$ in the smoothed graph, with their names in $[n]$ (the identifiers), the edges of the smoothed graph among them, the base-graph adjacency of every pair of them, and their private tapes. The rule is chosen for each $n$, so it may use $n$ and $p(n)$, and it is measurable in the tapes. The algorithm's output is the set of nodes whose bit is $1$.
--
--   Fix constants $\delta\in(0,\tfrac12]$ and $\sigma\in(0,1]$, and a function $p:\mathbb N\to\mathbb R$ with
--   $$
--   0\le p(n)\le \Big(\tfrac12-\delta\Big)\frac{\ln n}{n}\qquad\text{for all sufficiently large } n .
--   $$
--   For a base graph $G$ on $[n]$, the smoothed graph is the **addition-only smoothing** $\mathcal G=G\cup G(n,p)$: the pairs whose coin is $1$ are added to $G$. Then there are a constant $\eta>0$ and an $n_0$ with the following property. For every $n\ge n_0$, every budget
--   $$
--   T<\eta\,\frac{\ln n}{\ln\ln n},
--   $$
--   and every $T$-round randomized LOCAL algorithm with full information on $n$ nodes, there is a base graph $G$ on $[n]$ (chosen after the algorithm) for which
--   $$
--   \Pr_{\omega,\tau}\big[\text{the output set is an MIS of } \mathcal G\big]<\sigma .
--   $$
--   In words: an algorithm that computes an MIS of the smoothed graph with probability at least $\sigma$ on every base graph needs $\Omega(\log n/\log\log n)$ rounds. This holds even though the nodes know $n$ and $p$, use identifiers exactly in $[n]$, and can tell the edges of $G$ from the edges added by the smoothing. Together with Theorem 4.14, it shows that an $o(\log n/\log\log n)$-round algorithm needs smoothing parameter $p=\Theta(\ln n/n)$, up to a constant factor.
--
--   **Formalization Note** The constant $\eta$ depends on $\delta$, $\sigma$ and the function $p$, never on the algorithm. The coin law clamps $p(n)$ to $[0,1]$. On the theorem's range this clamp is the identity.
--
--   Differences from the source:
--   - generalization: p = p(n) ∈ [0, (1/2 − δ) ln n/n] (for every n) → 0 ≤ p n ≤ (1/2 − δ) ln n / n only for all sufficiently large n (∀ᶠ n in atTop); reason: a weaker hypothesis; the conclusion concerns only n ≥ n0, and the source's p satisfies it
--   - generalization: randomized LOCAL algorithm running T rounds, nodes knowing n and p, IDs exactly in [n], distinguishing edges of G from added edges → any rule measurable in the tapes whose output at v depends only on the radius-T ball of v in the smoothed graph: vertex names in Fin n, all smoothed edges inside the ball (including edges between two distance-T vertices), the G-adjacency of every pair in the ball, and the tapes on the ball; chosen per n; reason: every T-round LOCAL algorithm with the stated knowledge is an instance, so the lower bound over the larger class implies the source's; the view is at most what T + 1 rounds reveal, which the existential η absorbs
--   - encoding: requires Ω(log n/ log log n) rounds → ∃ η > 0, ∃ n0, ∀ n ≥ n0, ∀ T : ℕ with T < η ln n / ln ln n, ∀ algorithm with budget T, ∃ base graph G on Fin n with success probability < σ; reason: the meaning of Ω pinned by the proof (pp.38–39): a constant η such that every algorithm below η ln n/ln ln n fails for all large n; natural logarithms only rescale η
--   - encoding: computes an MIS with probability at least σ, over the smoothing and the private randomness → (coinLaw (Sym2 (Fin n)) (p n)).prod (tapeLaw (Fin n)) of the set of (ω, τ) where the output set is an MIS of the smoothed graph, compared with ENNReal.ofReal σ; reason: the joint law of the edge coins and the tapes; the success set is measurable (finitely many coin outcomes, outputs measurable in the tapes), so the measure is the probability
--   - encoding: graphs of n nodes, IDs exactly in [n] → SimpleGraph (Fin n); the vertex names are the identifiers; reason: Lean convention; G ranges over every graph on Fin n, which covers every assignment of IDs
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Theorem 5.1, p.30 (PDF p.32); proof §5.2–5.3, pp.32–39 (PDF pp.34–41)

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_SmoothedMIS_coinLaw
import Definitions.Def_SmoothedMIS_LocalAlg
import Definitions.Def_SmoothedMIS_smoothLaw
import Definitions.Def_SmoothedMIS_Supplement_FullInfoAlg

open MeasureTheory Filter

namespace SmoothedMIS.Supplement

/-- **Theorem 5.1** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for Distributed
MIS* (manuscript, sha256 dc2131db…), §5, p.30, PDF p.32): "Fix constants δ ∈ (0, 1/2] and
σ ∈ (0, 1], and let p = p(n) satisfy p ∈ [0, (1/2 − δ) ln n/n]. Any randomized LOCAL algorithm
that, for every graph G of n nodes computes an MIS of 𝒢 = G ∪ G(n, p), with probability at least
σ, requires Ω(log n/ log log n) rounds. The probability is over the smoothing and the
algorithm's private randomness. This bound holds even when nodes know the values of n, p, use IDs
exactly in [n], and can distinguish between edges of G and edges added by the smoothing."

**Formalization Note** Natural logarithms (`Real.log`). The smoothing coins are
`coinLaw (Sym2 (Fin n)) (p n)` (independent coins of probability `p(n)` on the vertex pairs), the
private tapes are `tapeLaw (Fin n)`, and the probability is over both jointly (the product
measure). Algorithms are `FullInfoAlg n T`: any rule whose output at `v` depends only on the
radius-`T` view of `v` (vertex names = IDs in `[n]`, the smoothed edges and the base-graph
adjacency inside the ball, the tapes on the ball), chosen after `n`, hence knowing `n` and `p`.
"Requires `Ω(log n / log log n)` rounds" is: there are `η > 0` and `n0` such that for every
`n ≥ n0`, every algorithm with budget `T < η ln n / ln ln n` fails, on some base graph `G` on
`n` nodes chosen after the algorithm, to output an MIS of the smoothed graph with probability at
least `σ`. The bound on `p` is assumed only for all sufficiently large `n`. `η` depends on
`δ`, `σ` and the function `p`, never on the algorithm.
The smoothed graph is `addSmooth G ω = G ∪ {e | ω e}`. -/
theorem theorem_5_1 (δ σ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hσ : 0 < σ ∧ σ ≤ 1) (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, 0 ≤ p n ∧ p n ≤ (1 / 2 - δ) * Real.log n / n) :
    ∃ η : ℝ, 0 < η ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ T : ℕ,
      (T : ℝ) < η * Real.log n / Real.log (Real.log n) →
      ∀ A : FullInfoAlg n T, ∃ G : SimpleGraph (Fin n),
        ((coinLaw (Sym2 (Fin n)) (p n)).prod (tapeLaw (Fin n)))
            {x | IsMIS (addSmooth G x.1) (A.outSet (addSmooth G x.1) G x.2)}
          < ENNReal.ofReal σ := by sorry

end SmoothedMIS.Supplement
