-- Prove2me | Theorems.Thm_SubsetConvFPRAS_lemma_2_5
-- name    : SubsetConvFPRAS.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:50.804103+00:00
-- url     : https://prove2.me/theorems/54b9db53-17fd-4b07-8683-aa0945e85207
-- title:
--   Lemma 2.5 — a small gradient of $\Phi$ makes complementary pairs likely
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$ be nonzero and $\gamma>0$. Suppose that for every $t\in(0,1]^U$ and $z\in\mathbb R^U_{>0}$ there is an irreducible chain on $\operatorname{supp}\pi_{t,z}$, reversible with respect to the soft intersection $\pi_{t,z}$, with spectral gap at least $\gamma$, whose moves update only one of the two sets $S,T$, and in which for every state and every $u\in S\oplus T$ the total rate of the moves removing the unique copy of $u$ is at most $1$. Then for every scalar $t\in(0,1]$ and every $z\in\mathbb R^U_{>0}$, with $y=\log z$ and $n=|U|$,
--   $$\pi_{t,z}(T\ne U\setminus S)\le n\Bigl(\|\nabla\Phi(y)\|_\infty+\frac{4\sqrt t}{\gamma}\Bigr).\tag{6}$$
--
--   Together with Lemma 5.5 ($\gamma=1$) this reduces finding a field that makes complementary pairs frequent to finding an approximate stationary point of the convex potential $\Phi$.
--
--   **Formalization Note** $\nabla\Phi(y)$ is written by the formula (4), $\partial_u\Phi=\pi_{t,z}(u\in S)-\pi_{t,z}(u\notin T)$; the verification file proves that this is the derivative of $\Phi$.
--
--   Differences from the source:
--   - encoding: ‖∇Φ(y)‖∞ → the maximum over u of |π_{t,z}(u ∈ S) − π_{t,z}(u ∉ T)|; reason: the formula (4) of the page; its agreement with the derivative of Φ is proved in the verification file
--   - encoding: moves removing the unique copy of u ∈ S ⊕ T → moves to states where u lies in neither set; reason: a move changes one set only, so these are exactly the removals of the unique copy
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), §2.3, Definition 2.4 and Lemma 2.5, pp.12–14 (restated p.23; proof pp.23–24)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_PairLaws

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Lemma 2.5, p.14 (restated p.23). If the soft intersections
have chains of spectral gap at least `γ > 0` as in `HasUniformGap`, then for every scalar `t ∈ (0,1]` and every
`z ∈ ℝ^U_{>0}`, with `y = log z`, `π_{t,z}(T ≠ U∖S) ≤ n (‖∇Φ(y)‖∞ + 4√t/γ)`, (6).

**Formalization Note.** `μ, ν` are the nonzero weights of §2.3, p.12, not assumed homogeneous. `softGradSup` is the
gradient norm through the formula (4); the verification file checks that formula against `softPhi`. -/
theorem lemma_2_5 {U : Type} [Fintype U] [DecidableEq U] (μ ν : Finset U → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (hν : ∀ S, 0 ≤ ν S) (hμ0 : ∃ S, μ S ≠ 0) (hν0 : ∃ S, ν S ≠ 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : HasUniformGap μ ν γ) (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1)
    (z : U → ℝ) (hz : ∀ u, 0 < z u) :
    nonComplementMass μ ν (fun _ => t) z ≤
      (Fintype.card U : ℝ) * (softGradSup μ ν (fun _ => t) z + 4 * Real.sqrt t / γ) := by sorry

end SubsetConvFPRAS
