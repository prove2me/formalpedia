-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_21
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:46:28.123662+00:00
-- url     : https://prove2.me/theorems/c8d9d682-b0f7-44d9-8649-6606c9ee66f5
-- title:
--   Theorem 4.21, p. 28 (corrected: d_G ≥ 1; measure for the order-2t truncation) — smallest eigenvalue under the FEC: λ_k^primal = λ⋆ and eigenvectors
-- statement:
--   Let $k\ge\max\{\lceil\deg F/2\rceil,\lceil\deg G/2\rceil\}$, let $S^\star_k$ be an optimal solution of (4.18), and suppose the flat extension condition (4.8) holds at an order $t$ (with $k_x=\max\{\deg F,\deg G\}$), with $d_G\ge1$. Then
--
--   1. the truncation $(S^\star_{k,\alpha})_{|\alpha|\le2t}$ admits a representing measure $\Phi^\star=\sum_{i=1}^rW_i\delta_{x^{(i)}}$ with $x^{(i)}\in\mathcal X$, $W_i\succeq0$ and $\sum_{i=1}^r\operatorname{tr}W_i=1$;
--   2. $\lambda_k^{\mathrm{primal}}=\lambda^\star$, and this value is $\mathscr L_{S^\star_k}(F)$;
--   3. for every such $\Phi^\star$ and every decomposition $W_i=\sum_{l=1}^{m_i}v^{(i,l)}(v^{(i,l)})^\top$,
--   $$F(x^{(i)})v^{(i,l)}=\lambda^\star v^{(i,l)},\qquad l=1,\dots,m_i,\ i=1,\dots,r.$$
--
--   That is, the smallest eigenvalue $\lambda^\star$ of $F$ over $\mathcal X$ is attained at the atoms $x^{(i)}$, with the $v^{(i,l)}$ as eigenvectors.
--
--   Differences from the source:
--   - correction: (i)–(iii) under the FEC alone → the additional premise 1 ≤ d_G (deg G ≥ 1); reason: for constant G (d_G = 0) the rank condition rank M_t(S) = rank M_{t−d_G}(S) is empty and the claim fails, e.g. G ≡ 1, n = m = 1, k = 2, S = (1, 0, 0, 0, 1): M_2(S) ⪰ 0 but no measure represents S; the proof applies Theorem 3.2/Theorem 3.1, which need an extension by at least one degree
--   - correction: S^{(k,⋆)} admits a representing measure (all moments |α| ≤ 2k) → the truncation (S_α)_{|α| ≤ 2t} at the order t of the FEC admits a representing measure; the extraction clauses quantify over every such measure; reason: the proof applies Theorem 3.2 at order t − d_G with extension of order t, so moments of order in (2t, 2k] are not constrained; this truncation is all that (ii)–(iv) use, since k_x ≤ 2t
--   - encoding: λ_k^primal = λ⋆; F(x⁽ⁱ⁾)v = λ⋆v → λ_k^primal = λ⋆ = 𝓛_{S⋆}(F) (EReal), and F(x⁽ⁱ⁾)v = 𝓛_{S⋆}(F)·v; reason: 𝓛_{S⋆}(F) is the attained optimal value of (4.18), so naming it adds nothing; it makes λ⋆ a real number in (iii)
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 28, Theorem 4.21

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.21 (p. 28): let `k ≥ max{⌈deg F/2⌉, ⌈deg G/2⌉}`, let `S⋆_k` be an optimal solution of
(4.18), and let the FEC (4.8) (with `k_x = max{deg F, deg G}`) hold at the order `t`, with
`d_G ≥ 1`. Then (i) the truncation `(S⋆_{k,α})_{|α| ≤ 2t}` admits a representing measure
`∑_i W_i δ_{x^{(i)}}`, `x^{(i)} ∈ 𝒳`, `W_i ⪰ 0`, with `∑_i tr(W_i) = 1`; (ii) `λ_k^primal = λ⋆`
(and this common value is `𝓛_{S⋆_k}(F)`); (iii) for every such measure and every decomposition
`W_i = ∑_l v^{(i,l)} (v^{(i,l)})ᵀ`, `F(x^{(i)}) v^{(i,l)} = λ⋆ v^{(i,l)}`. -/
theorem theorem_4_21 {n m q : ℕ} (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hF : F.IsSymm) (hG : G.IsSymm)
    (k : ℕ) (hk : max ((degMat F + 1) / 2) ((degMat G + 1) / 2) ≤ k)
    (S : MatSeq (Fin n) (Fin m)) (hS : IsLamPrimalOpt F G k S)
    (hdG : 1 ≤ dG G) (t : ℕ) (hFEC : FECAt (max (degMat F) (degMat G)) G k t S) :
    (∃ μ : AtomicMeasure m G, Represents μ t S ∧ ∑ i, (μ.W i).trace = 1) ∧
    (lamprimal F G k = lamstar F G ∧ lamstar F G = (riesz S F : EReal)) ∧
    (∀ μ : AtomicMeasure m G, Represents μ t S →
      ∀ (i : Fin μ.r) (mi : ℕ) (v : Fin mi → Fin m → ℝ), IsRankOneDecomp (μ.W i) v →
        ∀ l, F.map (eval (μ.pts i)) *ᵥ v l = riesz S F • v l) := by sorry

end RobustPMI.Hierarchy.Supplement
