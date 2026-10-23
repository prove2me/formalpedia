-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_14_3_1
-- name    : RamanujanLostNotebook.PartIV.entry_14_3_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T15:46:46.361631+00:00
-- url     : https://prove2.me/theorems/eb72f331-58c4-420c-9c38-f9a10569a021
-- title:
--   Self-reciprocal transformation of phi_w (real w > 0)
-- statement:
--   $\phi_w(t)=\frac{1}{\sqrt{w}}e^{-\pi t^2/(4w)}\phi_{1/w}(it/w)$. Here $\phi_w(t)=\int_0^\infty\frac{\cos(\pi t x)}{\cosh(\pi x)}e^{-\pi w x^2}dx$, $\psi_w(t)=\int_0^\infty\frac{\sin(\pi t x)}{\sinh(\pi x)}e^{-\pi w x^2}dx$, real $w>0$, $t\in\mathbb{C}$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 14, Entry 14.3.1, p. 309, eq. (14.3.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_ch14_phiW
open MeasureTheory

namespace RamanujanLostNotebook.PartIV
theorem entry_14_3_1 (w : ℝ) (hw : 0 < w) (t : ℂ) :
    phiW (w : ℂ) t = 1 / ((Real.sqrt w : ℝ) : ℂ) * Complex.exp (-((Real.pi : ℂ) * (t) ^ 2 / (4 * (w : ℂ)))) * phiW ((w⁻¹ : ℝ) : ℂ) (Complex.I * t / (w : ℂ)) := by sorry
end RamanujanLostNotebook.PartIV
