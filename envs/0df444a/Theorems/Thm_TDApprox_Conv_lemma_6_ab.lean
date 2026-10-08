-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_6_ab
-- name    : TDApprox.Conv.lemma_6_ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:38.651198+00:00
-- url     : https://prove2.me/theorems/ce7c6423-a80b-4e47-bc99-d958c77de7e4
-- title:
--   Lemma 6(a)–(b), p. 15 — E₀[φ(i_t)φ′(i_{t+m})] = ΦDP^mΦ′, bounded uniformly in m
-- statement:
--   Under Assumptions 1, 2 and 3, let $(i_t)_{t\in\mathbb Z}$ be a Markov chain with transition matrix $P$ that is already in steady state: $\Pr(i_a = s_0, \dots, i_{a+n} = s_n) = \pi(s_0)p_{s_0s_1}\cdots p_{s_{n-1}s_n}$. Write $E_0$ for expectation with respect to this chain. Then, for all $t \in \mathbb Z$ and $m \ge 0$:
--   1. (a) the expectations below are well defined and finite, and
--   $$E_0[\phi(i_t)\phi'(i_{t+m})] = \Phi D P^m \Phi',$$
--   where $(\Phi DP^m\Phi')_{kl} = \sum_i \pi(i)\phi_k(i)(P^m\phi_l)(i)$;
--   2. (b) there is a finite constant $G$ with $\|E_0[\phi(i_t)\phi'(i_{t+m})]\| \le G$ for all $t$ and $m$.
--
--   These identities convert steady-state correlations of the features into matrices built from $\Phi$, $D$ and $P$; part (b) is used to verify condition (g) of Theorem 2.
--
--   **Formalization Note.** The steady-state chain is any two-sided process on a probability space with the finite-dimensional distributions above. The matrix norm in (b) is the Frobenius norm, equivalent to the page's Euclidean induced norm; $G$ is existential, so the choice does not matter. Well-definedness covers the integrability of every entry, of $\phi_l$ under each $P^m(i)$, and the summability of the series defining $\Phi DP^m\Phi'$.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 6(a)–(b), p. 15 (stationary chain of Eq. (5), p. 15)

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 6(a)–(b)** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 15). Under Assumptions 1, 2
and 3, for the chain `(i_t)_{t ∈ ℤ}` in steady state:
(a) `E_0[φ(i_t)φ′(i_{t+m})] = ΦDP^mΦ′` for all `t, m`;
(b) there is a finite `G` with `‖E_0[φ(i_t)φ′(i_{t+m})]‖ ≤ G` for all `m`;
and each expression is well defined and finite. -/
theorem lemma_6_ab {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ) {N : ℕ} (σ : S → Fin N → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ) (h3 : Assumption3 P π g φ σ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i) :
    (∀ (t : ℤ) (m : ℕ),
      (∀ k l, Integrable (fun ω => φ (i t ω) k * φ (i (t + m) ω) l) μ) ∧
      (∀ j l, Integrable (fun x => φ x l) ((P ^ m) j)) ∧
      (∀ k l, Summable (fun j => (π {j}).toReal * φ j k * ∫ x, φ x l ∂((P ^ m) j))) ∧
      (fun k l => ∫ ω, φ (i t ω) k * φ (i (t + m) ω) l ∂μ) = phiDPmPhi P π φ m) ∧
    ∃ G : ℝ, ∀ (t : ℤ) (m : ℕ),
      frobNorm (fun k l => ∫ ω, φ (i t ω) k * φ (i (t + m) ω) l ∂μ) ≤ G := by sorry

end TDApprox.Conv
