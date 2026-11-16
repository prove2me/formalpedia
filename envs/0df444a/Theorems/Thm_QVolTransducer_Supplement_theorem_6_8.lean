-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_6_8
-- name    : QVolTransducer.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:41:25.366203+00:00
-- url     : https://prove2.me/theorems/d2175197-df59-4cab-b7f6-b5cb80c40658
-- title:
--   Theorem 6.8 — the induced discretization is irreducible, reversible and has $\varphi(P')\ge\varphi(P)$
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a measure space with $\Sigma$ countably generated, and let $P$ be a reversible, $\mu$-irreducible Markov kernel with stationary probability measure $\pi$. Let $\Omega=\Omega_1\sqcup\dots\sqcup\Omega_n$ be a $\Sigma$-measurable partition with $\mu(\Omega_j)>0$ for every $j$, and let $(\Omega',P')$ be the induced discretization:
--
--   $$\Omega'=\{j:\pi(\Omega_j)>0\},\qquad P'_{ij}=\frac1{\pi(\Omega_i)}\int_{\Omega_i}P(x,\Omega_j)\,d\pi(x).$$
--
--   Then $P'$ is irreducible, $P'$ is reversible with respect to $\pi'_i=\pi(\Omega_i)$, and
--
--   $$\varphi(P')\ge\varphi(P).$$
--
--   Conductance lower bounds therefore pass from a continuous walk to any finite discretization of this kind.
--
--   **Formalization Note** $\mu$-irreducibility uses $t\in\{1,2,\dots\}$ (Definition 6.2). The finite irreducibility and reversibility are the published `MarkovMixing.Irreducible` and `MarkovMixing.DetailedBalance`; conductances are valued in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: P reversible, with stationary probability measure π → P reversible with respect to the probability measure π (Definition 6.4); reason: reversibility with respect to π implies stationarity (Corollary 6.5), so stationarity is not a separate hypothesis
--   - encoding: irreducible (Definition 2.17: ∃ t ∈ ℕ = {1, 2, …} with (P′)^t_{ij} > 0) → MarkovMixing.Irreducible (∃ t ≥ 0); reason: they differ only on the diagonal, where for the stochastic matrix P′ a return in t ≥ 1 steps exists in either case
--   - encoding: conductances φ(P′) (Definition 2.24, min over S) and φ(P) (Definition 6.6) → values in [0, ∞], infima over the sets with 0 < π(S) < 1 (resp. 0 < π(A) < 1), +∞ if there is none; reason: the other sets have a zero denominator; [0, ∞] avoids Lean's sInf ∅ = 0
--   - encoding: a Σ-measurable finite partition (Ω_j)_{j=1}^n → n measurable, pairwise disjoint sets whose union is Ω; reason: same notion
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 6.8, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_QVolTransducer_Supplement_measCond

namespace QVolTransducer.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open Classical in
/-- **The induced discretization preserves irreducibility, reversibility and conductance**
(Cornelissen, Apers, Gribling, *Improved quantum volume estimation with transducers and amortized
quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 6.8, p.41
(PDF p.43)).

Let `(Ω, Σ, µ)` be a measure space with `Σ` countably generated, and `P` a reversible,
`µ`-irreducible Markov kernel with stationary probability measure `π`. Let `(Ω′, P′)` be the induced
discretization with respect to a `Σ`-measurable finite partition `Ω = Ω_1 ⊔ ⋯ ⊔ Ω_n` with
`µ(Ω_j) > 0` for every `j ∈ [n]`, where `Ω′ = {j : π(Ω_j) > 0}` and
`P′_{ij} = (1/π(Ω_i)) ∫_{Ω_i} P(x, Ω_j) dπ(x)`. Then `P′` is irreducible, `P′` is reversible with
respect to `π′_i = π(Ω_i)`, and `φ(P′) ≥ φ(P)`.

**Formalization Note** Reversibility of `P` is with respect to its stationary measure `π`
(Definition 6.4, which implies stationarity, Corollary 6.5); `µ`-irreducibility uses
`t ∈ ℕ = {1, 2, …}` (Definition 6.2). For the finite chain, irreducibility and reversibility are the
published `MarkovMixing.Irreducible` and `MarkovMixing.DetailedBalance`; `φ(P′)` is the finite
conductance of Definition 2.24 and `φ(P)` that of Definition 6.6, both in `[0, ∞]`. The partition
is given by `n` measurable, pairwise disjoint sets covering `Ω`. -/
theorem theorem_6_8 {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P] (π : Measure Ω) [IsProbabilityMeasure π]
    (hrev : IsReversibleWrt (fun x => P x) π) (hirr : IsIrreducibleWrt P μ)
    {n : ℕ} (parts : Fin n → Set Ω) (hmeas : ∀ j, MeasurableSet (parts j))
    (hdisj : Pairwise fun i j => Disjoint (parts i) (parts j)) (hcover : (⋃ j, parts j) = Set.univ)
    (hpos : ∀ j, 0 < μ (parts j)) :
    MarkovMixing.Irreducible (inducedP P π parts) ∧
    MarkovMixing.DetailedBalance (inducedP P π parts) (inducedStat π parts) ∧
    measCond (fun x => P x) π ≤ finCond (inducedP P π parts) (inducedStat π parts) := by sorry

end QVolTransducer.Supplement
