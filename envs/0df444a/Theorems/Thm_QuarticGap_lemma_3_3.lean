-- Prove2me | Theorems.Thm_QuarticGap_lemma_3_3
-- name    : QuarticGap.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:37.087544+00:00
-- url     : https://prove2.me/theorems/a7b68bbb-1d8d-4d6f-8fe3-1bdfdf73c18e
-- title:
--   Lemma 3.3 — a classical algorithm with at most $q_0(\xi,\delta)$ queries has $|\mathbb E F(f,J_A)| \le \tau_F(\xi,\delta)$
-- statement:
--   Let $\xi > 0$, $\delta \in (0,1)$, and let $f$ be uniformly random. Let $A$ be a randomized adaptive classical algorithm that queries values of $f$, makes at most $q \le q_0(\xi,\delta) = \lfloor\xi^2 M/(2\log(2K/\delta))\rfloor$ queries on every input and every run, and outputs $J_A \in Y$. Then
--   $$
--   |\mathbb E F_{\sin}(f,J_A)| \le \xi+\delta, \qquad |\mathbb E F_{\cos}(f,J_A)| \le \frac{\xi^2}{2}+\frac{q}{2M}+2\delta .
--   $$
--   In particular $|\mathbb E F(f,J_A)| \le \tau_F(\xi,\delta)$ for both tests, where $\tau_{\sin}(\xi,\delta) = \xi+\delta$ and $\tau_{\cos}(\xi,\delta) = \xi^2+2\delta$.
--
--   This is the core of the lower bound: at the output of a low-query algorithm the expectation of each test function is close to zero, at every adaptive strategy.
--
--   Differences from the source:
--   - encoding: a set of K characters → a nonempty Finset S with K = S.card; reason: the source divides by K and takes log(2K); K = 0 is meaningless
--   - encoding: Y ⊇ S → an embedding e of S into Y; reason: the source itself identifies S with coordinates of the outcome set
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins has perfect recall, so Kuhn gives the same law; the input reaches it only through the answers
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 3.3 and (11), (12), p.24

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap

/-- Lemma 3.3 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.24). Let `ξ > 0`, `δ ∈ (0, 1)`, and let `A`
be a randomized adaptive classical algorithm that queries values of `f`, makes at most
`q ≤ q₀(ξ, δ)` queries on every input and every run, and outputs `J_A ∈ Y`. For uniformly random `f`:
`|𝔼F_sin(f, J_A)| ≤ ξ + δ`, `|𝔼F_cos(f, J_A)| ≤ ξ²/2 + q/(2M) + 2δ`, and in particular
`|𝔼F(f, J_A)| ≤ τ_F(ξ, δ)` for both tests.

**Formalization Note** `A` is a general `QueryAlg`: adaptive and randomized. `K = |S|`. -/
theorem lemma_3_3 {m : ℕ} (hm : 2 ≤ m) (S : Finset (Qubits m)) (hS : S.Nonempty) {Y : Type*} [Fintype Y] (e : S ↪ Y)
    (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ ∧ δ < 1) (q : ℕ) (hq : q ≤ q0 m S.card ξ δ)
    (A : QueryAlg (Qubits m) ℤˣ Y) (hA : ∀ f, A.MakesAtMost (directRespond f) q) :
    |expF .sin e A| ≤ ξ + δ ∧
    |expF .cos e A| ≤ ξ ^ 2 / 2 + q / (2 * bigM m) + 2 * δ ∧
    |expF .sin e A| ≤ tauF .sin ξ δ ∧
    |expF .cos e A| ≤ tauF .cos ξ δ := by sorry

end QuarticGap
