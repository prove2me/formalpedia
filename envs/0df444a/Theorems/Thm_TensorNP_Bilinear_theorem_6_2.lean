-- Prove2me | Theorems.Thm_TensorNP_Bilinear_theorem_6_2
-- name    : TensorNP.Bilinear.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:10:36.798259+00:00
-- url     : https://prove2.me/theorems/9eb03497-d0bb-47fe-bfc4-dd9230d87679
-- title:
--   Theorem 6.2 — 3-colorability reduces to deciding whether $\sigma = 0$ is an $\ell^2$- or $\ell^3$-singular value
-- statement:
--   Let $F = \mathbb R$ or $F = \mathbb C$ and $p \in \{2, 3\}$. Graph 3-colorability is polynomial-time many-one reducible to the problem of deciding, for a rational tensor $\mathcal A$, whether $\sigma = 0$ is an $\ell^p$-singular value of $\mathcal A$ over $F$ (Definition 6.1):
--   $$
--   \textsf{3-COLORABILITY} \le_p \{\mathcal A : 0 \text{ is an } \ell^p\text{-singular value of } \mathcal A \text{ over } F\}
--   $$
--   for each of the four choices of $(F, p)$.
--
--   By the NP-completeness of 3-colorability (cited, not formalized), deciding whether $0$ is an $\ell^2$- or $\ell^3$-singular value of a tensor is NP-hard over $\mathbb R$ and over $\mathbb C$, which is the paper's statement.
--
--   **Formalization Note** "NP-hard" is rendered as a polynomial-time many-one reduction from 3-colorability, the reduction the paper's argument gives ("immediate from Theorem 3.7"). "($\ell^2$ or $\ell^3$)" is read as the claim for each of the two notions. Codes and polynomial-time computability are as in Theorem 3.7.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:22, Theorem 6.2; p. 0:21, Definition 6.1 and the remark after (21)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TensorNP_Bilinear_Encoding
import Definitions.Def_TensorNP_Bilinear_SingularValue

namespace TensorNP.Bilinear

open CookPvsNP

/-- Theorem 6.2 (p. 0:22): graph 3-colorability is polynomial-time many-one reducible to deciding
whether `σ = 0` is an ℓ²-singular value, and to deciding whether `σ = 0` is an ℓ³-singular
value, of a rational tensor, over `ℝ` and over `ℂ`. -/
theorem theorem_6_2 :
    PolyReducible TensorNP.Eigen.threeColLang (zeroL2SingLang ℝ) ∧ PolyReducible TensorNP.Eigen.threeColLang (zeroL2SingLang ℂ) ∧
      PolyReducible TensorNP.Eigen.threeColLang (zeroL3SingLang ℝ) ∧
        PolyReducible TensorNP.Eigen.threeColLang (zeroL3SingLang ℂ) := by sorry

end TensorNP.Bilinear
