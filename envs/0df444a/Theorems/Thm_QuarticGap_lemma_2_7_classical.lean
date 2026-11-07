-- Prove2me | Theorems.Thm_QuarticGap_lemma_2_7_classical
-- name    : QuarticGap.lemma_2_7_classical
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:12.480923+00:00
-- url     : https://prove2.me/theorems/9d245463-f5db-4994-a65f-b61fe6697a93
-- title:
--   Lemma 2.7, clause 1 — with known magnitudes, each classical input operation costs at most one query to $f$
-- statement:
--   Let $\{A(f)\}$ be a family of real matrices indexed by Boolean functions $f$ on $\{0,1\}^m$, in which every entry either does not depend on $f$ or equals $\mu_{ij} f(\sigma_{ij})$ for a fixed nonzero real $\mu_{ij}$ and a fixed point $\sigma_{ij}$. Then:
--
--   1. every entry magnitude, every row and column norm, the Frobenius norm and every sampling distribution of Definition 2.1 is independent of $f$;
--   2. every algorithm in the model of Definition 2.1 is simulated by an algorithm that queries $f$ directly, with the same output law on every $f$ and, for every $t$,
--   $$
--   P(\tau_{\mathrm{direct}} > t) \le P(\tau_{\mathrm{SQ}} > t).
--   $$
--
--   So a lower bound for direct queries, in the worst case or in expectation, is also a lower bound in the model of Definition 2.1. This is the reduction that lets the rest of the classical argument forget about matrices.
--
--   **Formalization Note** The simulating algorithm is a behaviour strategy, so it exists by mixing its own coins out given its transcript.
--
--   Differences from the source:
--   - generalization: a family whose map (i, j) ↦ σ_ij is computed by a fixed reversible circuit → no such hypothesis; reason: the Lean circuits may use any unitary gate, so the map is one gate; every family of the source is covered
--   - encoding: matrices of size N₁ × N₂ → any finite row and column types; reason: the same matrices
--   - reading: every input operation can be simulated with at most one query; a lower bound for direct queries is also a lower bound in Definition 2.1 → a direct-query algorithm with the same output law on every f and pointwise no larger query tails; reason: this form transfers worst-case and expected lower bounds at once
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 2.7, preamble and clause 1, p.18

import Mathlib
import Definitions.Def_QuarticGap_sqRespond

open QAlgorithms

namespace QuarticGap

/-- Lemma 2.7, preamble and clause 1 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.18). For a family
`{A(f)}` with known magnitudes, every entry magnitude, every row and column norm, the Frobenius norm
and every sampling distribution of Definition 2.1 is independent of `f`, and every classical input
operation can be simulated with at most one query to `f`: for every algorithm in the model of
Definition 2.1 there is an algorithm that queries `f` directly with the same output law on every `f`
and pointwise no larger query tails. A lower bound for direct queries, worst case or in expectation,
is therefore a lower bound in the model of Definition 2.1.

**Formalization Note** The reversible-circuit hypothesis of the source's preamble concerns gate
counts only and is not assumed here. The simulating algorithm has no private memory (see `QueryAlg`):
it exists by Kuhn's theorem, since its coins can be mixed out given its own transcript. -/
theorem lemma_2_7_classical {m : ℕ} {ρ κ Y : Type*} [Fintype ρ] [Fintype κ] (i₀ : ρ) (j₀ : κ)
    (A : (Qubits m → ℤˣ) → Matrix ρ κ ℝ) (hA : IsKnownMagnitudeFamily A) :
    (∀ f g i j, |A f i j| = |A g i j|) ∧
    (∀ f g i, rowNorm (A f) i = rowNorm (A g) i) ∧
    (∀ f g j, colNorm (A f) j = colNorm (A g) j) ∧
    (∀ f g, frobR (A f) = frobR (A g)) ∧
    (∀ f g (q : SQQuery ρ κ), (∀ i j, q ≠ SQQuery.entry i j) →
      sqRespond (A f) i₀ j₀ q = sqRespond (A g) i₀ j₀ q) ∧
    ∀ alg : QueryAlg (SQQuery ρ κ) (SQAns ρ κ) Y, ∃ alg' : QueryAlg (Qubits m) ℤˣ Y, ∀ f,
      (∀ j, alg'.outProb (directRespond f) j = alg.outProb (sqRespond (A f) i₀ j₀) j) ∧
      ∀ t, alg'.tailProb (directRespond f) t ≤ alg.tailProb (sqRespond (A f) i₀ j₀) t := by sorry

end QuarticGap
