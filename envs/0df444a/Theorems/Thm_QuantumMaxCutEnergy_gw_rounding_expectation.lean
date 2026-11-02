-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_gw_rounding_expectation
-- name    : QuantumMaxCutEnergy.gw_rounding_expectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T19:15:10.779588+00:00
-- url     : https://prove2.me/theorems/3efef512-93cb-457b-9e83-797b47a41323
-- title:
--   Goemans–Williamson rounding: expected cut $= \\sum w \\arccos\\langle v_i,v_j\\rangle/\\pi$
-- statement:
--   The Goemans–Williamson hyperplane rounding lemma for Quantum Max-Cut, stated inside the campaign's model.
--
--   Let $G$ be a finite graph with nonnegative rational edge weights and let $v_1,\dots,v_n \in \mathbb{R}^D$ ($D \ge 1$) be unit vectors — in the campaign's SDP-vector framework these are the vertex vectors extracted from a semidefinite relaxation of the Quantum Max-Cut energy. Let $g \in \mathbb{R}^D$ be a standard Gaussian vector and, for every vertex $i$, let $\sigma_i(g) = \operatorname{sign}\langle v_i, g\rangle \in \{-1, 0, 1\}$ be the sign of the hyperplane rounding. Then the expected value of the cut weight
--
--   $$C(g) = \sum_{\{i,j\} \in E} w_{ij}\,\mathbf{1}[\sigma_i(g) \ne \sigma_j(g)]$$
--
--   over the Gaussian $g$ is exactly
--
--   $$\mathbb{E}[C] = \sum_{\{i,j\} \in E} w_{ij}\,\frac{\arccos \langle v_i, v_j\rangle}{\pi}.$$
--
--   (The set where some $\langle v_i, g\rangle = 0$ has measure zero, so the sign convention there is immaterial.)
--
--   **Role in the campaign.** A cut is a computational-basis state, and its Quantum Max-Cut energy is its cut weight, so this identity converts an SDP-vector solution into the "cut-state" candidate of the Goemans–Williamson/GP family of roundings. Together with the scalar inequality $2\arccos t \ge \alpha\,\pi(1-t)$ it yields the $\alpha$-approximate cut state, the first of the two candidates in the level-2 analysis behind the campaign's $0.595$ entry.
--
--   **Formalization Note.** `Real.sign` is the real sign function; the model's `Edge` type carries the unordered pairs $i < j$ with rational weights; the integral is over Mathlib's `stdGaussian` on the Euclidean space $\mathbb{R}^D$.
-- source:
--   Michel X. Goemans and David P. Williamson, Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming, J. ACM 42 (1995), https://doi.org/10.1145/227683.227684 , Lemma (hyperplane rounding); Anshu-Gosset-Morenz, https://arxiv.org/abs/2003.14394 , Lemma 1 and Eq. (6); Gharibian-Parekh, https://arxiv.org/abs/1909.08846 , Section 3

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators
open MeasureTheory ProbabilityTheory

theorem QuantumMaxCutEnergy.gw_rounding_expectation (G : Input) (D : ℕ) (hD : 1 ≤ D)
    (v : Fin G.n → EuclideanSpace ℝ (Fin D))
    (hunit : ∀ i, ‖v i‖ = 1) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        (∑ e : Edge G.n, (G.weights e : ℝ) *
          (if Real.sign (inner ℝ (v e.val.1) g) = Real.sign (inner ℝ (v e.val.2) g) then 0 else 1))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin D))) =
    ∑ e : Edge G.n, (G.weights e : ℝ) * Real.arccos (inner ℝ (v e.val.1) (v e.val.2)) / Real.pi := by sorry
