-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_5_13
-- name    : TightQLB.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:25:57.224332+00:00
-- url     : https://prove2.me/theorems/e97e5454-3255-4ad9-8e75-529a2ca90a5a
-- title:
--   Theorem 5.13 — score bound: $\langle F,XF\rangle\le\beta_N+2\sqrt2\lambda(F)+72\lambda(F)^2$ for every unit $F\in P_{\le d}(H)$
-- statement:
--   Let $N=2^n$ with $n\ge1$, let $H$ be a finite-dimensional space with orthogonal projections $\{\Pi_z\}_{z\in[N]}$ summing to $I$, and let $X=\sum_zNp_z\Pi_z$, so that
--
--   $$
--   \langle F,XF\rangle=N\sum_z\mathbb E_\phi\big[p_z\|\Pi_zF(\phi)\|^2\big]
--   $$
--
--   is the expected score when $F$ is a final state. Then for every $d$ and every $F\in P_{\le d}(H)$ with $\|F\|^2=\mathbb E_\phi\|F(\phi)\|^2=1$,
--
--   $$
--   \langle F,XF\rangle\le\beta_N+2\sqrt2\,\lambda(F)+72\,\lambda(F)^2,
--   $$
--
--   where $\beta_N=2N/(N+1)$ and $\lambda$ is the progress measure.
--
--   This is the score half of Theorem 5.6: a constant improvement over the ideal score requires constant progress.
--
--   Differences from the source:
--   - encoding: F ∈ P_{≤d}(V), a polynomial of degree at most d in α, ᾱ, unit vector in L²(Haar) → IsPoly d F (a polynomial representative on unit vectors) and E_ϕ‖F(ϕ)‖² = 1, V the coordinate space of a finite type; reason: same objects
--   - encoding: λ(F) = (Σ_k k‖P_k F‖²)^{1/2} with P_k the projection onto the level-k blocks → progress F, with ‖P_k F‖ the supremum of |⟨G, F⟩| over unit-ball elements G of the span of the level-k blocks and a tsum over k; reason: this is the norm of the orthogonal projection onto the closed span, and the blocks are pairwise orthogonal, so it agrees with the projection inside P_{≤d}(V)
--   - encoding: Dir(a), density ∝ Π p_i^{a_i−1} with respect to the uniform measure on the simplex → weight Π p_i^{a_i−1} against the (N−1)-dimensional Hausdorff measure restricted to the simplex, divided by its total weight; reason: the normalization of the uniform measure cancels
--   - encoding: a Haar-random unit vector of C^N → the published haarTargetLaw (the standard Gaussian on C^N normalized); reason: the same law on unit vectors
--   - encoding: H = A ⊗ E with the output projections Π_z (acting on A) → any finite type V with orthogonal projections Π_z summing to I (IsProjFamily); reason: the same class: every such H gives such a family, and every such family is one with A = V and E trivial
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 5.13, p. 38 (PDF p. 41)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Level
open QAlgorithms

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 5.13 (Score bound)**, p.38 (PDF p.41).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"For every unit vector `F ∈ P_{≤d}(H)`, `⟨F, XF⟩ ≤ β_N + 2√2 λ(F) + 72 λ(F)²`."

**Formalization Note.**
* `H` is the coordinate space of a finite type `V`, with orthogonal projections `{Π_z}_{z∈[N]}` on
  it summing to `I` (`IsProjFamily`); `X = Σ_z N p_z Π_z` and `⟨F, XF⟩` is `scoreForm` (41).
* `F ∈ P_{≤d}(V)` is `IsPoly d F`; "unit vector" is `‖F‖² = E_ϕ‖F(ϕ)‖² = 1`.
* `λ` is `progress` (Definition 5.3); `β_N = 2N/(N + 1)`; `n ≥ 1` (§3.1). -/
theorem theorem_5_13 {n : ℕ} (hn : 1 ≤ n) {V : Type} [Fintype V] [DecidableEq V]
    (proj : Qubits n → Matrix V V ℂ) (hproj : IsProjFamily proj) (d : ℕ) (F : Fn n V)
    (hF : IsPoly d F) (hunit : hnormSq F = 1) :
    scoreForm proj F ≤ betaN n + 2 * Real.sqrt 2 * progress F + 72 * progress F ^ 2 := by sorry

end TightQLB.Supplement
