-- Prove2me | Theorems.Thm_QuantumPRC_theorem_7_1
-- name    : QuantumPRC.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:53.993043+00:00
-- url     : https://prove2.me/theorems/5e518e80-32d4-41d3-aa5e-87a730455a9e
-- title:
--   Theorem 7.1 (corrected: the radius is an input of the algorithms) — graph sampling and phase recovery
-- statement:
--   Fix a constant $p>0$. There are a PPT algorithm $\mathsf{GraphSample}(1^n,1^T)$ that outputs a simple graph $G$ on vertex set $[2n]$ with adjacency matrix $A$, and a deterministic polynomial-time algorithm $\mathsf{Recover}(1^T,G,e)$ that, given $G$ and $e\in\{0,1\}^{2n}$, outputs a $2n$-bit string, such that the following holds. For every sequence $n_k\to\infty$ and every sequence $T_k=o(n_k\log\log n_k/\log n_k)$ there is a negligible $\nu$ such that, for all sufficiently large $k$ and all $u,v\in\{0,1\}^{2n_k}$ with $|\mathrm{supp}(u)\cup\mathrm{supp}(v)|\le T_k$:
--
--   1. (induced-weight bound) every output graph of $\mathsf{GraphSample}(1^{n_k},1^{T_k})$ satisfies $\mathrm{wt}(v\oplus Au)\le p\,n_k$;
--   2. (recovery correctness) $\Pr_{G\leftarrow\mathsf{GraphSample}(1^{n_k},1^{T_k})}\big[\mathsf{Recover}(1^{T_k},G,v\oplus Au)=u\big]\ge1-\nu(n_k)$.
--
--   For a radius function $t(n)=o(n\log\log n/\log n)$ computable from $1^n$ in polynomial time, taking $n_k=k$ and $T_k=t(k)$ gives the printed theorem. This is the phase-error decoder of the PRIC construction.
--
--   Differences from the source:
--   - correction: fix a function t = o(n log log n/log n) (any function); then there exist (GraphSample, Recover) with the properties → the algorithms read the radius in unary and the properties hold along every sequence (n_k, T_k) with T_k = o(n_k log log n_k/log n_k); reason: the sampler of (220) must compute t(n); for a suitably chosen uncomputable t no pair of polynomial-time algorithms works (sketch, paper.md decision 7: a Bayes-error bound forces deg_G(i)·log log n/log n → ∞, the weight bound forces t·deg ≲ pn, and a diagonal choice of t defeats every pair); for computable t the corrected form gives the printed one
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 7.1, p.40 (restated p.63); Lemmas 8.7, 8.11, 8.12, pp.55, 59

import Mathlib
import Definitions.Def_QuantumPRC_GraphRecoverSpec

namespace QuantumPRC

/-- **Theorem 7.1** (graph sampling and phase recovery; corrected: the radius is an input of the
algorithms). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Theorem 7.1, p.40 (restated p.63):
"Fix a constant `p > 0`. Let `t : ℕ → ℕ` be a function satisfying `t(n) = o(n log log n / log n)`. There
exists a pair of algorithms `(GraphSample, Recover)` with the following properties. GraphSample is a
PPT algorithm that takes `1^n` as input and outputs a simple graph `G` on vertex set `[2n]` with adjacency
matrix `A`. Recover is a deterministic polynomial-time algorithm that takes `G` and `e ∈ {0,1}^{2n}` as
input and outputs a `2n`-bit string. For all sufficiently large `n` and all `u, v ∈ {0,1}^{2n}` satisfying
`|supp(u) ∪ supp(v)| ≤ t(n)`, the following hold. (i) Induced-weight bound. Every output graph satisfies
`wt(v ⊕ Au) ≤ pn`. (ii) Recovery correctness. `Pr_{G←GraphSample(1^n)}[Recover(G, v ⊕ Au) = u] ≥ 1 − negl(n)`."

**Formalization Note.** The algorithms also read the radius `T` in unary and the guarantee holds along
every sequence `(n_k, T_k)` with `n_k → ∞` and `T_k = o(n_k log log n_k / log n_k)`
(`GraphRecoverSpec`); for every radius function `t` computable in polynomial time this gives the
printed statement. The printed order (`t` fixed before the algorithms) cannot hold for every `t`:
the sampler of (220) must know `t(n)`. -/
theorem theorem_7_1 (p : ℝ) (hp : 0 < p) :
    ∃ (gc : ℕ → ℕ) (GS Rec : List Bool → List Bool), GraphRecoverSpec p gc GS Rec := by sorry

end QuantumPRC
