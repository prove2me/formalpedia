-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_cls_reduction_eventually
-- name    : UnaryQuadraticKKT.Hardness.unary_cls_reduction_eventually
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T03:51:31.358137+00:00
-- url     : https://prove2.me/theorems/d3fde8cb-f53e-43dd-ba9a-c37b5cf53211
-- title:
--   Unary quadratic-KKT reduces to 3D-Continuous-Localopt for all large answer bounds
-- statement:
--   There is a threshold $K$ such that for every $b\ge K$, the length-bounded unary exact quadratic-KKT problem reduces in polynomial time to the canonical 3D-Continuous-Localopt problem `clsSearch`:
--   $$\exists K\ \forall b\ge K:\ \mathrm{SearchReduces}\big(\mathrm{bounded}(U,b),\ \texttt{clsSearch}\big).$$
--   This is the reduction part of membership in CLS. The unary problem is a special case of the binary one, which lies in $\mathrm{CLS}=\mathrm{PPAD}\cap\mathrm{PLS}$ by Fearnley–Goldberg–Hollender–Savani.
--
--   **Formalization Note** Only sufficiently large $b$ is meaningful: for $b=0$ no answer fits the bound $(|a|+1)^0+0=1$, while `clsSearch` is total.
-- source:
--   Anagnostides–Panageas–Yan, The Complexity of KKT Points of Quadratic Programs with Polynomially-Bounded Coefficients, STOC 2027 submission #653 (October 2026), Theorem 4.1 (p.5), membership half; Fearnley–Goldberg–Hollender–Savani, arXiv:2311.13738v2, p.3 (KKT for QPs is in CLS) and arXiv:2011.01929 (CLS = PPAD ∩ PLS)

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace UnaryQuadraticKKT.Hardness
theorem unary_cls_reduction_eventually :
    ∃ K : ℕ, ∀ b : ℕ, K ≤ b → SearchReduces (bounded unarySearch b) clsSearch := by sorry
end UnaryQuadraticKKT.Hardness
