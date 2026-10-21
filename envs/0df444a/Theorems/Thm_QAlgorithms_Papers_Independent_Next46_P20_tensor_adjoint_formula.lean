-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_tensor_adjoint_formula
-- name    : QAlgorithms.Papers.Independent.Next46.P20.tensor_adjoint_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:16:03.960872+00:00
-- url     : https://prove2.me/theorems/9c644f75-237b-4af5-aad5-31e9bc874c46
-- title:
--   The tensor embedding adjoint is fiber contraction
-- statement:
--   Let $n\ge1$ and let $\chi\in L^2(\mathbb R^n)$ have norm one. For $T_\chi\psi(x,p)=\psi(x)\overline{\chi(p)}$, its Hilbert adjoint is defined on all of $L^2(\mathbb R^{2n})$ and obeys
--   $$
--   (T_\chi^*\Psi)(x)=\int_{\mathbb R^n}\Psi(x,p)\chi(p)\,dp
--   \quad\text{for almost every }x.
--   $$
--   The integrand is integrable for almost every fiber $x$. The inner product is conjugate-linear in its first argument.
--
--   This identifies the inverse contraction used in the phase-space representation.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 7, Theorem 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF pp.7–8, Theorem 2.3: the Hilbert adjoint contracts against chi,
without conjugating chi, with integrable fibers and equality a.e. in x. -/
theorem tensor_adjoint_formula {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (Psi : PhaseL2 n) :
    ∀ᵐ x : Configuration n,
      Integrable (fun p : Configuration n => Psi (phasePoint x p) * chi p) ∧
      (tensorEmbedding chi).adjoint Psi x =
        ∫ p : Configuration n, Psi (phasePoint x p) * chi p := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
