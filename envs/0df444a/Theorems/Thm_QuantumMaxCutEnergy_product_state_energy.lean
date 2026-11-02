-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_product_state_energy
-- name    : QuantumMaxCutEnergy.product_state_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T18:57:15.073078+00:00
-- url     : https://prove2.me/theorems/e81d0fa5-5255-47f4-b071-f44df16d53fa
-- title:
--   Energy of a product state: $2(1-|\\langle\\varphi_i,\\varphi_j\\rangle|^2)$ per edge
-- statement:
--   The energy identity for product states of the Quantum Max-Cut model.
--
--   Let $G$ be a finite graph on $\{1,\dots,n\}$ and let $\varphi_1,\dots,\varphi_n \in \mathbb{C}^2$ be one-qubit amplitude vectors, normalized so that $|\varphi_i(0)|^2 + |\varphi_i(1)|^2 = 1$ for every $i$. The product wave function
--
--   $$\psi(x) = \prod_{i=1}^{n} \varphi_i(x_i), \qquad x \in \{0,1\}^n,$$
--
--   is a normalized state, and on every edge $e = \{i,j\}$ its energy in the model's unnormalized form is
--
--   $$\sum_{x} \bigl| \psi(x) - \psi(x \circ \sigma_{ij}) \bigr|^2 = 2\Bigl(1 - \bigl|\langle \varphi_i, \varphi_j\rangle\bigr|^2\Bigr),$$
--
--   where $\sigma_{ij}$ swaps the two coordinates and $\langle \varphi_i, \varphi_j\rangle = \sum_a \overline{\varphi_i(a)}\,\varphi_j(a)$.
--
--   **Role in the campaign.** This is the bridge every product-state rounding argument passes through: a product state with Bloch directions $n_i$ has edge energy $w_e(1 - n_i\cdot n_j)/2$, exactly the objective of the classical MaxCut SDP. The product-state candidates of the AGM, Goemans–Williamson and Briët–de Oliveira Filho–Vallentin roundings (and hence the $0.526$/ $0.595$ entries' third candidate) are bounded by first producing amplitudes and then applying this identity.
--
--   **Formalization Note.** The proof expands $|a-b|^2 = \mathrm{Re}(\overline a a) + \mathrm{Re}(\overline b b) - 2\,\mathrm{Re}(\overline a b)$, splits the sum over $\{0,1\}^n$ into a product of one-coordinate sums (normality pins the coordinates outside the edge), and identifies the cross term with the two-site inner products.
-- source:
--   Standard product-state computation; the two-site form is Sevag Gharibian and Ojas Parekh, Almost Optimal Classical Approximation Algorithms for a Quantum Generalization of Max-Cut, APPROX/RANDOM 2019, https://arxiv.org/abs/1909.08846 (Eq. (6)) and the rounding analysis of Anshu-Gosset-Morenz, TQC 2020, https://arxiv.org/abs/2003.14394 (Section 2)

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.product_state_energy (G : QuantumMaxCutEnergy.Input) (φ : Fin G.n → Bool → ℂ)
    (hunit : ∀ i, Complex.normSq (φ i true) + Complex.normSq (φ i false) = 1) :
    (∑ x : Fin G.n → Bool, Complex.normSq (∏ i, φ i (x i))) = 1 ∧
      ∀ e : QuantumMaxCutEnergy.Edge G.n, (∑ x : Fin G.n → Bool,
          Complex.normSq ((∏ i, φ i (x i)) -
            (∏ i, φ i (x ((Equiv.swap e.val.1 e.val.2) i))))) =
        2 * (1 - Complex.normSq (∑ a : Bool, star (φ e.val.1 a) * φ e.val.2 a)) := by sorry
