-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_schwartzWeyl_composition
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.schwartzWeyl_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:43:25.057165+00:00
-- url     : https://prove2.me/theorems/b6dc62bc-1734-4a01-9533-4688b1764c55
-- title:
--   Schwartz-symbol Weyl composition and common twisted convolution
-- statement:
--   Let $n\ge1$ and let $a_\sigma,b_\sigma\in\mathcal S(Z)$ be Schwartz twisted symbols on $Z=\mathbb R^{2n}$. Define ordinary and phase-space Weyl operators by $(2\pi)^{-n}\int a_\sigma(u)T(u)\,du$ and $(2\pi)^{-n}\int a_\sigma(u)T_{\rm ph}(u)\,du$, respectively, and likewise for $b_\sigma$. Here $T(u)$ is the ordinary Weyl translation and $T_{\rm ph}(u)F(z)=e^{-i\sigma(z,u)/2}F(z-u)$. There exists a Schwartz common twisted symbol
--
--   $$c_\sigma(z)=(2\pi)^{-n}\int_Z e^{i\sigma(z,u)/2}a_\sigma(z-u)b_\sigma(u)\,du$$
--
--   such that $A B=C$ on $\mathcal S(\mathbb R^n)$ and $A_{\rm ph}B_{\rm ph}=C_{\rm ph}$ on $\mathcal S(Z)$, where $C,C_{\rm ph}$ are the corresponding Weyl operators with twisted symbol $c_\sigma$.
--
--   This is the well-defined Schwartz-symbol instance of Proposition 19 and the p.7 composition assertion. It makes no claim about composing arbitrary tempered-symbol operators. Explicitly, $\sigma((x,p),(x',p'))=p\cdot x'-p'\cdot x$ and $T(x_0,p_0)f(x)=e^{i(p_0\cdot x-p_0\cdot x_0/2)}f(x-x_0)$.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 35, Proposition 19: well-defined Schwartz-symbol instance

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF pp.7,35, Proposition 19, its expressly restricted Schwartz-symbol
instance. The common twisted symbol is an actual Schwartz function given by
an integrable convolution; both ordinary and phase-space operators compose.
This does not assert the undefined product of arbitrary tempered symbols. -/
theorem schwartzWeyl_composition (n : ℕ) (hn : 0 < n)
    (a b : SchwartzMap (PhaseSpaceGrouped n) ℂ) :
    ∃ c : SchwartzMap (PhaseSpaceGrouped n) ℂ,
      (∀ z, c z = twistedConvolution a b z) ∧
      (∀ f : SchwartzMap (ConfigurationEuclidean n) ℂ,
        configurationWeylFromTwisted a (configurationWeylFromTwisted b f) =
          configurationWeylFromTwisted c f) ∧
      (∀ F : SchwartzMap (PhaseSpaceGrouped n) ℂ,
        phaseWeylFromTwisted a (phaseWeylFromTwisted b F) =
          phaseWeylFromTwisted c F) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
