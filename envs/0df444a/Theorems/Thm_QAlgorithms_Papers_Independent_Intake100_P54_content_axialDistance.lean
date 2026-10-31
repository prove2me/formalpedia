-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P54_content_axialDistance
-- name    : QAlgorithms.Papers.Independent.Intake100.P54.content_axialDistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:49:02.920128+00:00
-- url     : https://prove2.me/theorems/b1939f0f-0986-4788-b462-3f650bc6dcce
-- title:
--   §6.1, equation (6.2): content and axial-distance identities
-- statement:
--   Let $(\gamma,J)$ be a nonempty type $A$ local region with $\gamma\in\mathbb Z^n$ weakly increasing, and realize it as a numbered configuration of boxes with contents $c(b_k)=\gamma_k$. Let $p$ be a standard configuration filling and $w_p(k)=p(b_k)$ its word. Write $b(p(i))=b_{w_p^{-1}(i)}$ for the box containing entry $i$, with row and column coordinates $(r_i,c_i)$; the column coordinate $c_i$ is distinct notation from the content function $c(b)$. For every entry $i$ and every pair $i,j$,
--
--   $$(w_p\gamma)_i=\gamma_{w_p^{-1}(i)}=c(b(p(i))),$$
--
--   $$d_{ji}(p)=c_j-c_i+r_i-r_j=c(b(p(j)))-c(b(p(i)))=\langle w_p\gamma,\varepsilon_j-\varepsilon_i\rangle.$$
--
--   Here $(w\gamma)_i=\gamma_{w^{-1}(i)}$ and $d_{ji}$ is the axial distance from $j$ to $i$. These identities connect the classical signed distance with the root axial distance; they apply in particular to placed skew shapes.
-- source:
--   Affine Hecke algebras and generalized standard Young tableaux, arXiv:math/0401329v2, PDF p. 27, §6.1, equation (6.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P54

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P54

/-- Equation (6.2) and §6.1, PDF pp.27–28: inverse-word coordinates equal
the contents of the boxes containing each entry; the signed classical
axial-distance formula equals the root axial distance. This includes the
configuration extension noted in §5.10, with integer dominant contents. -/
theorem content_axialDistance {n : ℕ} (gamma : Fin n → ℤ)
    (hgamma : Monotone gamma) (J : Set (ARoot n))
    (hlocal : (aRegion (fun i => (gamma i : ℝ)) J).Nonempty)
    (D : BoxDrawing n) (hD : ConfigurationFor gamma J D)
    (p : ConfigurationTableaux D) :
    (∀ i : Fin n,
      aWeightAction (fun k => (gamma k : ℝ)) (tableauWord p.val) i =
        (gamma ((tableauWord p.val).symm i) : ℝ) ∧
      (gamma ((tableauWord p.val).symm i) : ℝ) =
        drawingContent D (boxContaining p.val i)) ∧
    (∀ i j : Fin n,
      classicalAxialDistance D p.val j i =
        drawingContent D (boxContaining p.val j) - drawingContent D (boxContaining p.val i) ∧
      drawingContent D (boxContaining p.val j) - drawingContent D (boxContaining p.val i) =
        aAxialDistance (fun k => (gamma k : ℝ)) (tableauWord p.val) j i) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P54

end
