-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_18
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:45:19.286025+00:00
-- url     : https://prove2.me/theorems/045b7b90-669d-4bb1-aaa9-ba7546ee1f87
-- title:
--   Theorem 4.18, pp. 26–27 (corrected: d_G ≥ 1; measure for the order-2t truncation) — robust polynomial SDP under the FEC (4.8)
-- statement:
--   For (RPSDP) and its relaxations (4.14)–(4.15), let $S^{(k,\star)}$ and $y^{(k,\star)}$ be optimal solutions of (4.14) and (4.15) for some $k\ge\lceil k_x/2\rceil$, suppose the flat extension condition (4.8) holds at an order $\lceil k_x/2\rceil\le t\le k$ with $d_G\ge1$, and assume (RPSDP) has an optimal solution. Then:
--
--   1. the truncation $(S^{(k,\star)}_\alpha)_{|\alpha|\le2t}$ admits a representing measure $\Phi^\star=\sum_{i=1}^rW_i\delta_{x^{(i)}}$ with $x^{(i)}\in\mathcal X$, $W_i\succeq0$;
--   2. $\tau_k^{\mathrm{primal}}\le\tau^\star$, with equality if $\mathcal X$ is compact and Assumption 3 holds.
--
--   Consequently, if $\mathcal X$ is compact, Assumption 3 holds and $\tau_k^{\mathrm{primal}}=\tau_k^{\mathrm{dual}}$, then $\tau_k^{\mathrm{primal}}=\tau_k^{\mathrm{dual}}=\tau^\star$ and
--
--   3. $y^{(k,\star)}$ is an optimal solution of (RPSDP);
--   4. for every such $\Phi^\star$ and every decomposition $W_i=\sum_{l=1}^{m_i}v^{(i,l)}(v^{(i,l)})^\top$,
--   $$\Big(\sum_{j=1}^\ell P_j(x^{(i)})y^{(k,\star)}_j-P_0(x^{(i)})\Big)v^{(i,l)}=0.$$
--
--   Differences from the source:
--   - correction: (i)–(iv) under the FEC alone → the additional premise 1 ≤ d_G (deg G ≥ 1); reason: for constant G (d_G = 0) the rank condition rank M_t(S) = rank M_{t−d_G}(S) is empty and the claim fails, e.g. G ≡ 1, n = m = 1, k = 2, S = (1, 0, 0, 0, 1): M_2(S) ⪰ 0 but no measure represents S; the proof applies Theorem 3.2/Theorem 3.1, which need an extension by at least one degree
--   - correction: S^{(k,⋆)} admits a representing measure (all moments |α| ≤ 2k) → the truncation (S_α)_{|α| ≤ 2t} at the order t of the FEC admits a representing measure; the extraction clauses quantify over every such measure; reason: the proof applies Theorem 3.2 at order t − d_G with extension of order t, so moments of order in (2t, 2k] are not constrained; this truncation is all that (ii)–(iv) use, since k_x ≤ 2t
--   - reading: the theorem's own hypotheses ((RPSDP) is a special case of (RPMIO), whose optimal set is assumed nonempty on p. 2) → hypothesis ∃ y, IsOptSDP c P0 Pv G y; reason: the p. 2 standing assumption governs every statement about τ⋆; without it the real infimum τ⋆ is a junk value
--   - encoding: 'S^{(k,⋆)} optimal', 'FEC: ∃ t', values in ℝ ∪ {±∞} → IsTauPrimalOpt / IsTauDualOpt; a universally quantified t with FECAt; EReal values; reason: same instances
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 26, Theorem 4.18

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.18 (p. 26): let `S^{(k,⋆)}` and `y^{(k,⋆)}` be optimal solutions of (4.14) and (4.15)
for some `k ≥ ⌈k_x/2⌉`, and let the FEC (4.8) hold at the order `⌈k_x/2⌉ ≤ t ≤ k`, with
`d_G ≥ 1`. Then (i) the truncation `(S^{(k,⋆)}_α)_{|α| ≤ 2t}` admits a representing measure
`∑_i W_i δ_{x^{(i)}}`, `x^{(i)} ∈ 𝒳`, `W_i ⪰ 0`; (ii) `τ_k^primal ≤ τ⋆`, with equality if `𝒳` is
compact and Assumption 3 holds. Consequently, if moreover `𝒳` is compact, Assumption 3 holds and
`τ_k^primal = τ_k^dual`, then `τ_k^primal = τ_k^dual = τ⋆`, (iii) `y^{(k,⋆)}` is optimal for
(RPSDP), and (iv) for every such measure and every decomposition
`W_i = ∑_l v^{(i,l)} (v^{(i,l)})ᵀ`,
`(∑_j P_j(x^{(i)}) y^{(k,⋆)}_j − P_0(x^{(i)})) v^{(i,l)} = 0`. -/
theorem theorem_4_18 {ℓ n m q : ℕ} (c : Fin ℓ → ℝ)
    (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP0 : P0.IsSymm) (hPv : ∀ i, (Pv i).IsSymm) (hG : G.IsSymm)
    (hmin : ∃ y, IsOptSDP c P0 Pv G y)
    (k : ℕ) (hk : (kxSDP P0 Pv G + 1) / 2 ≤ k)
    (S : MatSeq (Fin n) (Fin m)) (hS : IsTauPrimalOpt c P0 Pv G k S)
    (y : Fin ℓ → ℝ) (hy : IsTauDualOpt c P0 Pv G k y)
    (hdG : 1 ≤ dG G) (t : ℕ) (hFEC : FECAt (kxSDP P0 Pv G) G k t S) :
    (∃ μ : AtomicMeasure m G, Represents μ t S) ∧
    (tauprimal c P0 Pv G k ≤ (taustar c P0 Pv G : EReal) ∧
      (IsCompact (Xset G) → Assumption3SDP P0 Pv G →
        tauprimal c P0 Pv G k = (taustar c P0 Pv G : EReal))) ∧
    (IsCompact (Xset G) → Assumption3SDP P0 Pv G →
      tauprimal c P0 Pv G k = taudual c P0 Pv G k →
      tauprimal c P0 Pv G k = (taustar c P0 Pv G : EReal) ∧
      taudual c P0 Pv G k = (taustar c P0 Pv G : EReal) ∧
      IsOptSDP c P0 Pv G y ∧
      ∀ μ : AtomicMeasure m G, Represents μ t S →
        ∀ (i : Fin μ.r) (mi : ℕ) (v : Fin mi → Fin m → ℝ), IsRankOneDecomp (μ.W i) v →
          ∀ l, (lmi P0 Pv y).map (eval (μ.pts i)) *ᵥ v l = 0) := by sorry

end RobustPMI.Hierarchy.Supplement
