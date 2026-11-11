-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_4_2
-- name    : QuadStatRE.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:46:36.744441+00:00
-- url     : https://prove2.me/theorems/697fb2cf-1c2e-433b-81de-8e289e82cfac
-- title:
--   Lemma 4.2 — RM(1,4) sharing is three-multiplicative
-- statement:
--   Let $a,b,c\in\mathbb F_2$ be shared using the RM scheme: with affine polynomials $p_a(u)=a+\alpha\cdot u$, $p_b(u)=b+\beta\cdot u$, $p_c(u)=c+\gamma\cdot u$ on $\mathbb F_2^4$ ($\alpha,\beta,\gamma\in\mathbb F_2^4$), the shares at position $u\in I=\mathbb F_2^4\setminus\{0\}$ are $a_u=p_a(u)$, $b_u=p_b(u)$, $c_u=p_c(u)$. Then the coordinatewise product vector is an additive sharing of $abc$:
--   $$\bigoplus_{u\in I}a_ub_uc_u=abc.$$
--
--   Together with the additive sharing of $w$, this makes the XOR of the fifteen child targets equal the parent target (4.2), which is why the RM step preserves correctness.
--
--   **Formalization Note.** The identity is stated for every choice of the linear parts, i.e. for every sharing, not only on average.
--
--   Differences from the source:
--
--   - encoding: a, b, c shared using the RM scheme (a uniformly random affine p_a with p_a(0) = a) → shares a + α·u for an arbitrary α ∈ F₂⁴ (likewise b, c); reason: the claimed identity is about each sharing in the support of the scheme
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
--   - encoding: bits {0,1} and F₂ → ZMod 2; reason: the same field
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 22, Lemma 4.2

import Mathlib
import Definitions.Def_QuadStatRE_Main_RMSharing
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 4.2 (Three-multiplicativity), p. 22: if `a, b, c ∈ F₂` are shared with the RM scheme, by
affine polynomials `p_a(u) = a + α·u`, `p_b(u) = b + β·u`, `p_c(u) = c + γ·u`, then
`⊕_{u ∈ I} a_u b_u c_u = abc`. -/
theorem lemma_4_2 (a b c : F2) (α β γ : Fin 4 → F2) :
    ∑ k : Fin 15, rmShare a α k * rmShare b β k * rmShare c γ k = a * b * c := by sorry

end QuadStatRE.Main
