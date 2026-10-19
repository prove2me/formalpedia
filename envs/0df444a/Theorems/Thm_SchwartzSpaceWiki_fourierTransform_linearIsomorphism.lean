-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_fourierTransform_linearIsomorphism
-- name    : SchwartzSpaceWiki.fourierTransform_linearIsomorphism
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:18:13.241987+00:00
-- url     : https://prove2.me/theorems/54700cf4-fab5-4323-8c9b-404420a08c90
-- title:
--   The Fourier transform is a linear isomorphism $\mathcal{S}(\mathbb{R}^n)\to\mathcal{S}(\mathbb{R}^n)$
-- statement:
--   The Fourier transform $(\mathcal{F}f)(\xi)=\int_{\mathbb{R}^n} e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$ is a linear isomorphism of $\mathcal{S}(\mathbb{R}^n)$ onto itself: it maps $\mathcal{S}(\mathbb{R}^n)$ into $\mathcal{S}(\mathbb{R}^n)$, it is injective on $\mathcal{S}(\mathbb{R}^n)$, every element of $\mathcal{S}(\mathbb{R}^n)$ is the Fourier transform of some element of $\mathcal{S}(\mathbb{R}^n)$, and $\mathcal{F}(f+cg)=\mathcal{F}f+c\,\mathcal{F}g$ for all $f,g\in\mathcal{S}(\mathbb{R}^n)$, $c\in\mathbb{C}$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), lead paragraph ("the Fourier transform is an automorphism on this space") and section "Properties — Analytic properties", 3rd bullet ("The Fourier transform is a linear isomorphism F : 𝒮(ℝⁿ) → 𝒮(ℝⁿ)")

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem fourierTransform_linearIsomorphism (n : ℕ) :
    Set.BijOn fourierTransform (schwartzSpace n) (schwartzSpace n) ∧
    ∀ f ∈ schwartzSpace n, ∀ g ∈ schwartzSpace n, ∀ c : ℂ,
      fourierTransform (f + c • g) = fourierTransform f + c • fourierTransform g := by sorry

end SchwartzSpaceWiki
