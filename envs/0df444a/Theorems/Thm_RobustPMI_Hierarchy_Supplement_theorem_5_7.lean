-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_5_7
-- name    : RobustPMI.Hierarchy.Supplement.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:48:34.447802+00:00
-- url     : https://prove2.me/theorems/e0642a8c-35fa-4cdc-93c5-eeb73ed6c700
-- title:
--   Theorem 5.7, p. 31 (corrected: d_G ≥ 1 in (ii)) — non-convex setting: a rank-one moment matrix certifies f_k^dual ≥ f⋆ and extracts a minimizer
-- statement:
--   Let $s^{(k,\star)}$ be a minimizer of (5.2) for some $k\ge\max\{\lceil k_x/2\rceil,\lceil k_y/2\rceil\}$, and assume (RPMIO) has an optimal solution (no convexity is assumed).
--
--   1. If $\operatorname{rank}M_{\lceil k_y/2\rceil}(s^{(k,\star)})=1$, then $f_k^{\mathrm{dual}}\ge f^\star$ and the truncation $\hat s^{(k,\star)}=(s^{(k,\star)}_\alpha)_{|\alpha|\le2\lceil k_y/2\rceil}$ admits a Dirac representing measure $\delta_{y^\star}$ for some $y^\star\in\mathcal Y$, i.e. $s^{(k,\star)}_\alpha=(y^\star)^\alpha$ for $|\alpha|\le2\lceil k_y/2\rceil$.
--   2. If moreover $(\rho^\star_k,S^{(k,\star)})$ is an optimal solution of (5.1) satisfying (5.3) with $d_G\ge1$, and $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}$, then $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}=f^\star$ and every such $y^\star$ is a minimizer of (RPMIO).
--
--   Differences from the source:
--   - correction: (ii) under the FEC alone → the additional premise 1 ≤ d_G (deg G ≥ 1); reason: for constant G (d_G = 0) the rank condition rank M_t(S) = rank M_{t−d_G}(S) is empty and the claim fails, e.g. G ≡ 1, n = m = 1, k = 2, S = (1, 0, 0, 0, 1): M_2(S) ⪰ 0 but no measure represents S; the proof applies Theorem 3.2/Theorem 3.1, which need an extension by at least one degree
--   - reading: (ii) 'if the condition (5.3) holds' → (ii) for an optimal solution (ρ⋆_k, S^{(k,⋆)}) of (5.1) satisfying (5.3); reason: (5.3) is a condition on S^{(k,⋆)} from Theorem 5.4, which the proof of (ii) invokes
--   - generalization: (ii) y⋆ (the point from (i)) is a minimizer → every y⋆ ∈ 𝒴 whose Dirac measure represents ŝ^{(k,⋆)} is a minimizer; reason: for ⌈k_y/2⌉ ≥ 1 such y⋆ is unique (y⋆ = s_e), so this is the source claim; for ⌈k_y/2⌉ = 0 it also covers the other points
--   - reading: the theorem's own hypotheses (the paper assumes once, on p. 2, that the optimal set of (RPMIO) is nonempty) → hypothesis ∃ y, IsGlobalMin f θ P G y; reason: the p. 2 standing assumption governs every statement about f⋆; without it the real infimum f⋆ is a junk value
--   - encoding: values in ℝ ∪ {±∞} → EReal; reason: Lean convention
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 31, Theorem 5.7

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 5.7 (p. 31): let `s^{(k,⋆)}` be a minimizer of (5.2) for some
`k ≥ max{⌈k_x/2⌉, ⌈k_y/2⌉}`.
(i) If `rank M_{⌈k_y/2⌉}(s^{(k,⋆)}) = 1`, then `f_k^dual ≥ f⋆` and the truncation
`ŝ^{(k,⋆)} = (s^{(k,⋆)}_α)_{|α| ≤ 2⌈k_y/2⌉}` admits a Dirac representing measure `δ_{y⋆}` for some
`y⋆ ∈ 𝒴`.
(ii) If moreover `(ρ⋆_k, S^{(k,⋆)})` is an optimal solution of (5.1) satisfying (5.3) (with
`d_G ≥ 1`) and `f_k^primal = f_k^dual`, then `f_k^primal = f_k^dual = f⋆` and every such `y⋆` is a
minimizer of (RPMIO). -/
theorem theorem_5_7 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm) (hmin : ∃ y, IsGlobalMin f θ P G y)
    (k : ℕ) (hkx : (kx P G + 1) / 2 ≤ k) (hky : (ky f θ P + 1) / 2 ≤ k)
    (sv : (Fin ℓ →₀ ℕ) → ℝ) (hs : IsDualMinimizer5 f θ P G k sv) :
    ((momentMat ((ky f θ P + 1) / 2) (scalarSeq sv)).rank = 1 →
      (fstar f θ P G : EReal) ≤ fdual5 f θ P G k ∧
        ∃ ystar ∈ Yset θ, ∀ α ∈ monos (σ := Fin ℓ) (2 * ((ky f θ P + 1) / 2)),
          sv α = eval ystar (monomial α (1 : ℝ))) ∧
    (∀ (ρ : ℝ) (S : MatSeq (Fin n) (Fin m)), IsPrimalOpt5 f θ P G k ρ S →
      ∀ t₁ : ℕ, 1 ≤ dG G → FECAt (kx P G) G k t₁ S →
      (momentMat ((ky f θ P + 1) / 2) (scalarSeq sv)).rank = 1 →
      fprimal5 f θ P G k = fdual5 f θ P G k →
      fprimal5 f θ P G k = (fstar f θ P G : EReal) ∧
        fdual5 f θ P G k = (fstar f θ P G : EReal) ∧
        ∀ ystar ∈ Yset θ, (∀ α ∈ monos (σ := Fin ℓ) (2 * ((ky f θ P + 1) / 2)),
          sv α = eval ystar (monomial α (1 : ℝ))) → IsGlobalMin f θ P G ystar) := by sorry

end RobustPMI.Hierarchy.Supplement
