-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_5_4
-- name    : RobustPMI.Hierarchy.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:48:08.724684+00:00
-- url     : https://prove2.me/theorems/6c349574-eb7c-4367-8570-ff37fae89f6f
-- title:
--   Theorem 5.4, pp. 29–30 (corrected: d_G, d_Θ ≥ 1; measures for the order-2t₁, 2t₂ truncations) — convex setting under the FECs (5.3)–(5.4)
-- statement:
--   Let $(\rho^\star_k,S^{(k,\star)})$ and $s^{(k,\star)}$ be optimal solutions of (5.1) and (5.2) for some $k\ge\max\{\lceil k_x/2\rceil,\lceil k_y/2\rceil\}$, assume (RPMIO) has an optimal solution, and let $d_\Theta=\max_j\lceil\deg\theta_j/2\rceil$. Consider the flat extension conditions
--   $$\exists\,\lceil k_x/2\rceil\le t_1\le k:\ \operatorname{rank}M_{t_1}(S^{(k,\star)})=\operatorname{rank}M_{t_1-d_G}(S^{(k,\star)}),\tag{5.3}$$
--   $$\exists\,\lceil k_y/2\rceil\le t_2\le k:\ \operatorname{rank}M_{t_2}(s^{(k,\star)})=\operatorname{rank}M_{t_2-d_\Theta}(s^{(k,\star)}).\tag{5.4}$$
--
--   1. If (5.3) holds and $d_G\ge1$, the truncation of order $2t_1$ of $S^{(k,\star)}$ admits a representing measure $\Phi^\star=\sum_{i=1}^{r_1}W_i\delta_{x^{(i)}}$ with $x^{(i)}\in\mathcal X$, $W_i\succeq0$, and $f_k^{\mathrm{primal}}\le f^\star$.
--   2. Under Assumption 5, if (5.4) holds and $d_\Theta\ge1$, the truncation of order $2t_2$ of $s^{(k,\star)}$ admits a representing probability measure $\mu^\star=\sum_{j=1}^{r_2}\lambda_j\delta_{y^{(j)}}$ with $y^{(j)}\in\mathcal Y$ and $\lambda_j>0$, and $f_k^{\mathrm{dual}}\ge f^\star$.
--
--   Consequently, under (5.3), (5.4) (with $d_G,d_\Theta\ge1$) and Assumption 5, if $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}$, then
--
--   3. $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}=f^\star$;
--   4. for every such $\mu^\star$, $\sum_{j=1}^{r_2}\lambda_jy^{(j)}$ is an optimal solution of (RPMIO);
--   5. for every such $\mu^\star$ and $\Phi^\star$ and every decomposition $W_i=\sum_lv^{(i,l)}(v^{(i,l)})^\top$,
--   $$P\Big(\sum_{j=1}^{r_2}\lambda_jy^{(j)},x^{(i)}\Big)v^{(i,l)}=0.$$
--
--   Differences from the source:
--   - correction: (i), (iii)–(v) under the FEC alone → the additional premise 1 ≤ d_G (deg G ≥ 1); reason: for constant G (d_G = 0) the rank condition rank M_t(S) = rank M_{t−d_G}(S) is empty and the claim fails, e.g. G ≡ 1, n = m = 1, k = 2, S = (1, 0, 0, 0, 1): M_2(S) ⪰ 0 but no measure represents S; the proof applies Theorem 3.2/Theorem 3.1, which need an extension by at least one degree
--   - correction: (ii), (iii)–(v) under the FEC (5.4) alone → the additional premise 1 ≤ d_Θ; reason: if every θ_j is constant (in particular s = 0) then d_Θ = 0, the rank condition (5.4) is empty and s^{(k,⋆)} need not have a representing measure (same counterexample as for d_G with m = 1); the proof applies Theorem 3.2, which needs an extension by one degree
--   - correction: S^{(k,⋆)} admits a representing measure (all moments |α| ≤ 2k) → the truncation (S_α)_{|α| ≤ 2t₁} at the order t₁ of the FEC admits a representing measure; the extraction clauses quantify over every such measure; reason: the proof applies Theorem 3.2 at order t₁ − d_G with extension of order t₁, so moments of order in (2t₁, 2k] are not constrained; this truncation is all that (ii)–(iv) use, since k_x ≤ 2t₁
--   - correction: s^{(k,⋆)} admits a representing probability measure (all moments up to 2k) → the truncation of order 2t₂ of s^{(k,⋆)} admits it; (iv)–(v) quantify over every such measure; reason: the FEC (5.4) only constrains moments up to order 2t₂; f, θ_j and P have y-degree ≤ k_y ≤ 2t₂, which is all the proof uses
--   - reading: the theorem's own hypotheses (the paper assumes once, on p. 2, that the optimal set of (RPMIO) is nonempty) → hypothesis ∃ y, IsGlobalMin f θ P G y; reason: the p. 2 standing assumption governs every statement about f⋆; without it the real infimum f⋆ is a junk value
--   - encoding: optimal solutions, '∃ t₁', '∃ t₂', values in ℝ ∪ {±∞} → IsPrimalOpt5 / IsDualMinimizer5; universally quantified t₁, t₂; EReal values; reason: same instances
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 29, Theorem 5.4

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 5.4 (pp. 29–30): let `(ρ⋆_k, S^{(k,⋆)})` and `s^{(k,⋆)}` be optimal solutions of (5.1)
and (5.2) for some `k ≥ max{⌈k_x/2⌉, ⌈k_y/2⌉}`. With the FECs
(5.3) `∃ ⌈k_x/2⌉ ≤ t₁ ≤ k`, `rank M_{t₁}(S^{(k,⋆)}) = rank M_{t₁−d_G}(S^{(k,⋆)})` and
(5.4) `∃ ⌈k_y/2⌉ ≤ t₂ ≤ k`, `rank M_{t₂}(s^{(k,⋆)}) = rank M_{t₂−d_Θ}(s^{(k,⋆)})`:
(i) if (5.3) holds (and `d_G ≥ 1`), the truncation of order `2t₁` of `S^{(k,⋆)}` admits a
representing measure `∑_i W_i δ_{x^{(i)}}` on `𝒳`, and `f_k^primal ≤ f⋆`;
(ii) under Assumption 5, if (5.4) holds (and `d_Θ ≥ 1`), the truncation of order `2t₂` of
`s^{(k,⋆)}` admits a representing probability measure `∑_j λ_j δ_{y^{(j)}}`, `y^{(j)} ∈ 𝒴`,
`λ_j > 0`, and `f_k^dual ≥ f⋆`.
Consequently, under (5.3), (5.4) and Assumption 5, if `f_k^primal = f_k^dual`, then
(iii) `f_k^primal = f_k^dual = f⋆`; and for all such measures (iv) `∑_j λ_j y^{(j)}` is an optimal
solution of (RPMIO) and (v) `P(∑_j λ_j y^{(j)}, x^{(i)}) v^{(i,l)} = 0` for every decomposition
`W_i = ∑_l v^{(i,l)} (v^{(i,l)})ᵀ`. -/
theorem theorem_5_4 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm) (hmin : ∃ y, IsGlobalMin f θ P G y)
    (k : ℕ) (hkx : (kx P G + 1) / 2 ≤ k) (hky : (ky f θ P + 1) / 2 ≤ k)
    (ρ : ℝ) (S : MatSeq (Fin n) (Fin m)) (hS : IsPrimalOpt5 f θ P G k ρ S)
    (sv : (Fin ℓ →₀ ℕ) → ℝ) (hs : IsDualMinimizer5 f θ P G k sv) :
    (∀ t₁ : ℕ, 1 ≤ dG G → FECAt (kx P G) G k t₁ S →
      (∃ μ : AtomicMeasure m G, Represents μ t₁ S) ∧
        fprimal5 f θ P G k ≤ (fstar f θ P G : EReal)) ∧
    (Assumption5 f θ P G → ∀ t₂ : ℕ, 1 ≤ dTheta θ →
      (ky f θ P + 1) / 2 ≤ t₂ → t₂ ≤ k →
      (momentMat t₂ (scalarSeq sv)).rank = (momentMat (t₂ - dTheta θ) (scalarSeq sv)).rank →
      (∃ ν : AtomicProb θ, ∀ α ∈ monos (σ := Fin ℓ) (2 * t₂), sv α = ν.moments α) ∧
        (fstar f θ P G : EReal) ≤ fdual5 f θ P G k) ∧
    (Assumption5 f θ P G → ∀ t₁ t₂ : ℕ, 1 ≤ dG G → 1 ≤ dTheta θ →
      FECAt (kx P G) G k t₁ S →
      (ky f θ P + 1) / 2 ≤ t₂ → t₂ ≤ k →
      (momentMat t₂ (scalarSeq sv)).rank = (momentMat (t₂ - dTheta θ) (scalarSeq sv)).rank →
      fprimal5 f θ P G k = fdual5 f θ P G k →
      fprimal5 f θ P G k = (fstar f θ P G : EReal) ∧
        fdual5 f θ P G k = (fstar f θ P G : EReal) ∧
        ∀ ν : AtomicProb θ, (∀ α ∈ monos (σ := Fin ℓ) (2 * t₂), sv α = ν.moments α) →
          IsGlobalMin f θ P G ν.barycenter ∧
          ∀ μ : AtomicMeasure m G, Represents μ t₁ S →
            ∀ (i : Fin μ.r) (mi : ℕ) (v : Fin mi → Fin m → ℝ), IsRankOneDecomp (μ.W i) v →
              ∀ l, evalP P ν.barycenter (μ.pts i) *ᵥ v l = 0) := by sorry

end RobustPMI.Hierarchy.Supplement
