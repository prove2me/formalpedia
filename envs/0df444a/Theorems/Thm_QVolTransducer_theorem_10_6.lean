-- Prove2me | Theorems.Thm_QVolTransducer_theorem_10_6
-- name    : QVolTransducer.theorem_10_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:55.146622+00:00
-- url     : https://prove2.me/theorems/4924b0bb-afea-4fdb-b765-6ac860bc734f
-- title:
--   Theorem 10.6 — quantum volume estimation with $\tilde O(d^{5/4}(\sqrt d+R)/\varepsilon+d^2)$ membership queries
-- statement:
--   Let $B_d$ be the closed Euclidean unit ball of $\mathbb R^d$. There are constants $C>0$ and $k\in\mathbb N$ with the following property. For all integers $d\ge4$ and reals $R\ge1$, $0<\varepsilon<1$ there is a quantum query algorithm — a finite list of query points $x_1,\dots,x_m\in\mathbb R^d$, a workspace, a number $T$ of queries, input-independent unitaries and a readout of the measured registers, all fixed before the body — that makes
--
--   $$
--   T\ \le\ C\Bigl(\frac{d^{5/4}(\sqrt d+R)}{\varepsilon}+d^2\Bigr)\bigl(\log(2+d)\,\log(2+R)\,\log(2+1/\varepsilon)\bigr)^{k}
--   $$
--
--   membership queries $O_K:|i,b\rangle\mapsto|i,b\oplus[x_i\in K]\rangle$ and, for every convex body $K$ (compact and convex) with $B_d\subseteq K\subseteq RB_d$, outputs a real $\tilde V$ with
--
--   $$
--   \Bigl|\frac{\tilde V}{\mathrm{Vol}(K)}-1\Bigr|\le\varepsilon
--   $$
--
--   with probability at least $2/3$.
--
--   This is the paper's main formal result; combined with the classical rounding of Jia, Laddha, Lee and Vempala it yields the headline bound $\tilde O(d^{3.5}+d^{1.75}/\varepsilon)$ for general convex bodies.
--
--   **Formalization Note** The algorithm is the published `QAlgorithms.QueryAlg` with the standard (XOR) query to the membership bits of its query points. The positivity $\tilde V>0$ of the problem statement follows from $|\tilde V/\mathrm{Vol}(K)-1|\le\varepsilon<1$.
--
--   Differences from the source:
--   - reading: membership queries at points of ℝ^d (concretely the phase oracles O_{K,ζ}, O_{K,ζ/γ} on two grids) → XOR queries to the membership bits of finitely many query points fixed, with the algorithm and its readout, before K; reason: the grids are one choice of points; a phase query is a bit query on a |−⟩ target and a bit query is a phase query on a doubled point set (paper.md decision 2)
--   - reading: Õ(·) hiding polylogarithmic factors in d, R and 1/ε → ∃ C > 0, k ∈ ℕ fixed before d, R, ε with T ≤ C·(d^{5/4}(√d+R)/ε + d²)·(log(2+d)·log(2+R)·log(2+1/ε))^k for all parameters; reason: the literal §2.1 definition uses log R, which vanishes at R = 1 (paper.md decision 3)
--   - encoding: bounded-error quantum algorithm → success probability ≥ 2/3 for every admissible K; reason: Q(P) := Q_{1/3}(P) (Definition 2.1) and Algorithm 2's "Success probability: At least 2/3"
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 10.6, p.72 (PDF p.74); problem statement p.1 (PDF p.3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_memOracle

namespace QVolTransducer

open QAlgorithms MeasureTheory

open Classical in
/-- **Quantum volume estimation** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 10.6, p.72 (PDF p.74): "Let 4 ≤ d ∈ ℕ, R ≥ 1 and 0 < ε < 1.
Then, there is a bounded-error quantum algorithm that returns an ε-relative estimate of Vol(K) with
a number of membership queries that satisfies Õ(d^{5/4}(√d + R)/ε + d²), where the tilde hides
polylogarithmic factors in d, R and 1/ε"; the problem is stated on p.1).

There are constants `C > 0` and `k ∈ ℕ` such that for all `d ≥ 4`, `R ≥ 1` and `0 < ε < 1` there
is a quantum query algorithm — finitely many query points `pts` in `ℝ^d`, a workspace, `T`
queries, input-independent unitaries and a readout `out` of the measured registers, all fixed
before the body — with
`T ≤ C (d^{5/4}(√d + R)/ε + d²) (log(2+d) log(2+R) log(2+1/ε))^k`, which for every convex body
`B_d ⊆ K ⊆ RB_d` outputs `Ṽ` with `|Ṽ/Vol(K) − 1| ≤ ε` with probability at least `2/3`.

**Formalization Note** The algorithm is the published `QAlgorithms.QueryAlg` with the standard
(XOR) query to the membership bits of the points `pts` (`memOracle`); a phase query `O_{K,ζ}` is one
bit query on a `|−⟩` target. The tilde is read with all-parameter (not only asymptotic) bounds and
`log(2+·)` factors, since the paper's §2.1 definition with `log R` degenerates at `R = 1`. Every
`d`, `R`, `ε` is covered; `C` and `k` are fixed before them. -/
theorem theorem_10_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (d : ℕ) (R ε : ℝ), 4 ≤ d → 1 ≤ R → 0 < ε → ε < 1 →
      ∃ (m w T : ℕ) (pts : Fin m → EuclideanSpace ℝ (Fin d))
        (A : QueryAlg (Fin m) Bool (Fin w) T) (out : (Fin m × Bool) × Fin w → ℝ),
        (T : ℝ) ≤ C * ((d : ℝ) ^ ((5 : ℝ) / 4) * (Real.sqrt d + R) / ε + (d : ℝ) ^ 2) *
            (Real.log (2 + d) * Real.log (2 + R) * Real.log (2 + 1 / ε)) ^ k ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
          Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
          2 / 3 ≤ probEvent (A.finalState (memOracle pts K))
            (fun z => |out z / (volume K).toReal - 1| ≤ ε) := by sorry

end QVolTransducer
