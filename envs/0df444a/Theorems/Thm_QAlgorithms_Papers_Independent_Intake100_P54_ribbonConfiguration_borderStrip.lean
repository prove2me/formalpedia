-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P54_ribbonConfiguration_borderStrip
-- name    : QAlgorithms.Papers.Independent.Intake100.P54.ribbonConfiguration_borderStrip
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:49:50.951565+00:00
-- url     : https://prove2.me/theorems/ac087b83-cfc1-4f28-88a6-f297433ff462
-- title:
--   Proposition 6.6: ribbon configurations are border strips
-- statement:
--   Let $\gamma=(\gamma_1\le\cdots\le\gamma_n)\in\mathbb Z^n$, and let $(\gamma,J)$ be a placed ribbon shape in type $A_{n-1}$. Thus its chamber set $F^{(\gamma,J)}$ is nonempty and $\langle\gamma,\alpha\rangle\ne0$ for every root $\alpha$. Let $D$ be the associated placed box configuration. Then
--
--   $$D\text{ is a placed skew diagram and contains at most one box on each content diagonal}.$$
--
--   Such a diagram is a placed border strip in the convention of §6.5. Connectivity is not required. This identifies the paper's ribbon regions with the corresponding classical border-strip geometry.
-- source:
--   Affine Hecke algebras and generalized standard Young tableaux, arXiv:math/0401329v2, PDF p. 30, Proposition 6.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P54

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P54

/-- Proposition 6.6, PDF p.30 (border-strip convention p.29): a dominant
integral ribbon gives a geometrically skew configuration with at most one
box on each diagonal. Disconnected border strips and n=0 are permitted. -/
theorem ribbonConfiguration_borderStrip {n : ℕ} (gamma : Fin n → ℤ)
    (hgamma : Monotone gamma) (J : Set (ARoot n))
    (hribbon : IsRibbonA (fun i => (gamma i : ℝ)) J)
    (D : BoxDrawing n) (hD : ConfigurationFor gamma J D) :
    IsPlacedBorderStrip D := by sorry

end QAlgorithms.Papers.Independent.Intake100.P54

end
