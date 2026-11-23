-- Prove2me | Theorems.Thm_PlatonicJEPA_spectral_jepa_unique_up_to_rotation
-- name    : PlatonicJEPA.spectral_jepa_unique_up_to_rotation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:16:18.145799+00:00
-- url     : https://prove2.me/theorems/d7be8b3c-519e-4029-aec5-2e5818a9fe9f
-- title:
--   Proposition 1: spectral JEPAs are unique up to rotation
-- statement:
--   Let $\ell(a,b)=\|a-b\|^2$, let $\Omega$ whiten the embeddings, and let $1\le k<|Z|$. Then the spectral objective has a minimiser, and its minimum is
--
--   $$\min L_\pi=2\sum_{i=1}^k(1-\mu_i).$$
--
--   If $\mu_k>\mu_{k+1}$ (with $\mu_{|Z|}:=-\infty$), the minimisers are exactly the whitened embeddings $h$ for which every coordinate $\sqrt{p}\,h_i$ lies in the span of the eigenvectors of $K_\pi$ with eigenvalue at least $\mu_k$. These are the rotations $Q\Phi_\pi$, $Q\in O(k)$, of the spectral embedding $\Phi_\pi(z)=(v_1(z),\dots,v_k(z))/\sqrt{p(z)}$, so any two minimisers differ by a rotation.
--
--   **Formalization Note** The paper's description "exactly $Q\Phi_\pi$" is stated as the equivalent condition on the coordinates, which does not require choosing eigenvectors.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2.1, Proposition 1, p. 3

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem spectral_jepa_unique_up_to_rotation {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π) (hk : 1 ≤ k) (hkZ : k < Fintype.card Z) :
    (∃ h : Z → Fin k → ℝ, IsSpectralMin p π h) ∧
    (∀ h : Z → Fin k → ℝ, IsSpectralMin p π h →
      predLoss π h = 2 * ∑ i ∈ Finset.Icc 1 k, (1 - eigs p π i)) ∧
    ((k + 1 < Fintype.card Z → eigs p π (k + 1) < eigs p π k) →
      (∀ h : Z → Fin k → ℝ, IsSpectralMin p π h ↔
        (IsWhitened p h ∧ ∀ i : Fin k, (fun z => Real.sqrt (p z) * h z i) ∈ topSpace p π k)) ∧
      (∀ h h' : Z → Fin k → ℝ, IsSpectralMin p π h → IsSpectralMin p π h' →
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h' z = rot Q (h z))) := by sorry

end PlatonicJEPA
