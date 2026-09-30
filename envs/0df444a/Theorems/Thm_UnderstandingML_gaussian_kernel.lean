-- Prove2me | Theorems.Thm_UnderstandingML_gaussian_kernel
-- name    : UnderstandingML.gaussian_kernel
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:48:25.996388+00:00
-- url     : https://prove2.me/theorems/77bf6f09-4bcb-4d52-80e1-2874812809ff
-- title:
--   Example 16.2: on ℝ, ψ(x)ₙ = e^{−x²/2} xⁿ/√n! into ℓ² has ⟨ψ(x), ψ(x')⟩ = e^{−(x−x')²/2}; the Gaussian kernel e^{−‖x−x'‖²/(2σ)} on ℝⁿ is a kernel
-- statement:
--   **Example 16.2 (Gaussian Kernel).** Let the original instance space be $\mathbb{R}$ and consider the mapping $\psi$ where for each $n \ge 0$ there is an element $\psi(x)_n = \frac{1}{\sqrt{n!}}e^{-x^2/2}x^n$. Then $\langle\psi(x), \psi(x')\rangle = e^{-(x-x')^2/2}$. More generally, given $\sigma > 0$, the Gaussian kernel $K(x, x') = e^{-\|x - x'\|^2/(2\sigma)}$ implements an inner product in a (infinite-dimensional) feature space.
--
--   Formally: the map into $\ell^2$ with the stated inner products, and `IsKernel` for the Gaussian kernel on $\mathbb{R}^n$ for every $\sigma > 0$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.2 pp. 220-221, Example 16.2 with its derivation and the general Gaussian kernel

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Example 16.2 (Gaussian Kernel)** (pp. 220–221). On `ℝ`, the mapping `ψ` with coordinates
`ψ(x)ₙ = (1/√n!) e^{−x²/2} xⁿ` into `ℓ²` satisfies `⟨ψ(x), ψ(x')⟩ = e^{−(x − x')²/2}`; more
generally, for every `σ > 0` the Gaussian kernel `K(x, x') = e^{−‖x − x'‖²/(2σ)}` on `ℝ^n`
implements an inner product in some Hilbert space. -/
theorem gaussian_kernel :
    (∃ ψ : ℝ → lp (fun _ : ℕ ↦ ℝ) 2,
      ∀ x x' : ℝ, ⟪ψ x, ψ x'⟫_ℝ = Real.exp (-((x - x') ^ 2) / 2)) ∧
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → IsKernel (gaussianKernel (n := n) σ) := by sorry

end UnderstandingML
