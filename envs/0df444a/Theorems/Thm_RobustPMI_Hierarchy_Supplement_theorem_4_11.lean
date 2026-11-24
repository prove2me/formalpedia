-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_11
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:43:19.771923+00:00
-- url     : https://prove2.me/theorems/56d707cf-9a8d-458a-97ef-fe8043f4e998
-- title:
--   Theorem 4.11, p. 21 (corrected: d_G ≥ 1; measure for the order-2t truncation) — finite convergence and extraction under the FEC (4.8)
-- statement:
--   Let $(f_k^{\mathrm{primal}},S^{(k,\star)})$ and $s^{(k,\star)}$ be optimal solutions of (4.4) and (4.5) for some $k\ge\lceil k_x/2\rceil$, and suppose the flat extension condition
--   $$\lceil k_x/2\rceil\le t\le k,\qquad \operatorname{rank}M_t(S^{(k,\star)})=\operatorname{rank}M_{t-d_G}(S^{(k,\star)})\tag{4.8}$$
--   holds, with $d_G\ge1$. Assume that (RPMIO) has an optimal solution. Then:
--
--   1. the truncation $(S^{(k,\star)}_\alpha)_{|\alpha|\le2t}$ admits a representing measure $\Phi^\star=\sum_{i=1}^rW_i\delta_{x^{(i)}}\in\mathfrak M^m_+(\mathcal X)$ with $x^{(i)}\in\mathcal X$, $W_i\succeq0$;
--   2. $f_k^{\mathrm{primal}}\le f^\star$, with equality under Assumptions 1 and 3.
--
--   Consequently, under Assumptions 1 and 3, if $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}$, then $f_k^{\mathrm{primal}}=f_k^{\mathrm{dual}}=f^\star$ and
--
--   3. $s^{(k,\star)}_e=(s^{(k,\star)}_{e_1},\dots,s^{(k,\star)}_{e_\ell})$ is an optimal solution of (RPMIO);
--   4. for every such $\Phi^\star$ and every decomposition $W_i=\sum_{l=1}^{m_i}v^{(i,l)}(v^{(i,l)})^\top$,
--   $$P\big(s^{(k,\star)}_e,x^{(i)}\big)v^{(i,l)}=0,\qquad l=1,\dots,m_i,\ i=1,\dots,r.$$
--
--   The flat extension condition is a checkable certificate that the hierarchy has converged at order $k$ and lets one read off a minimizer and the active constraints.
--
--   Differences from the source:
--   - correction: (i)–(iv) under the FEC alone → the additional premise 1 ≤ d_G (deg G ≥ 1); reason: for constant G (d_G = 0) the rank condition rank M_t(S) = rank M_{t−d_G}(S) is empty and the claim fails, e.g. G ≡ 1, n = m = 1, k = 2, S = (1, 0, 0, 0, 1): M_2(S) ⪰ 0 but no measure represents S; the proof applies Theorem 3.2/Theorem 3.1, which need an extension by at least one degree
--   - correction: S^{(k,⋆)} admits a representing measure (all moments |α| ≤ 2k) → the truncation (S_α)_{|α| ≤ 2t} at the order t of the FEC admits a representing measure; the extraction clauses quantify over every such measure; reason: the proof applies Theorem 3.2 at order t − d_G with extension of order t, so moments of order in (2t, 2k] are not constrained; this truncation is all that (ii)–(iv) use, since k_x ≤ 2t
--   - reading: the theorem's own hypotheses (the paper assumes once, on p. 2, that the optimal set of (RPMIO) is nonempty) → hypothesis ∃ y, IsGlobalMin f θ P G y; reason: the p. 2 standing assumption governs every statement about f⋆; without it the real infimum f⋆ is a junk value
--   - encoding: '(f_k^primal, S^{(k,⋆)}) optimal', 'FEC: ∃ t' → IsPrimalOpt (feasible with ρ = f_k^primal); ∃ t in the hypothesis as a universally quantified t with FECAt; reason: same instances
--   - encoding: extended values of the relaxations → EReal sSup/sInf, compared with the real f⋆ coerced to EReal; reason: Lean convention; low orders can be infeasible or unbounded
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 21, Theorem 4.11

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.11 (p. 21): let `(f_k^primal, S^{(k,⋆)})` and `s^{(k,⋆)}` be optimal solutions of
(4.4) and (4.5) for some `k ≥ ⌈k_x/2⌉`, and let the FEC (4.8) hold at the order
`⌈k_x/2⌉ ≤ t ≤ k`, with `d_G ≥ 1`. Then
(i) the truncation `(S^{(k,⋆)}_α)_{|α| ≤ 2t}` admits a representing measure
`Φ⋆ = ∑_i W_i δ_{x^{(i)}}`, `x^{(i)} ∈ 𝒳`, `W_i ⪰ 0`;
(ii) `f_k^primal ≤ f⋆`, with equality under Assumptions 1 and 3.
Consequently, under Assumptions 1 and 3, if `f_k^primal = f_k^dual` then
`f_k^primal = f_k^dual = f⋆`, (iii) `s_e^{(k,⋆)}` is an optimal solution of (RPMIO), and
(iv) for every such `Φ⋆` and every decomposition `W_i = ∑_l v^{(i,l)} (v^{(i,l)})ᵀ`,
`P(s_e^{(k,⋆)}, x^{(i)}) v^{(i,l)} = 0`. -/
theorem theorem_4_11 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm) (hmin : ∃ y, IsGlobalMin f θ P G y)
    (k : ℕ) (hk : (kx P G + 1) / 2 ≤ k)
    (ρ : ℝ) (S : MatSeq (Fin n) (Fin m)) (hS : IsPrimalOpt f θ P G k ρ S)
    (sv : (Fin ℓ →₀ ℕ) → ℝ) (hs : IsDualMinimizer f θ P G k sv)
    (hdG : 1 ≤ dG G) (t : ℕ) (hFEC : FECAt (kx P G) G k t S) :
    (∃ μ : AtomicMeasure m G, Represents μ t S) ∧
    (fprimal f θ P G k ≤ (fstar f θ P G : EReal) ∧
      (Assumption1 f θ P G → Assumption3 θ P G →
        fprimal f θ P G k = (fstar f θ P G : EReal))) ∧
    (Assumption1 f θ P G → Assumption3 θ P G → fprimal f θ P G k = fdual f θ P G k →
      fprimal f θ P G k = (fstar f θ P G : EReal) ∧ fdual f θ P G k = (fstar f θ P G : EReal) ∧
      IsGlobalMin f θ P G (sE sv) ∧
      ∀ μ : AtomicMeasure m G, Represents μ t S →
        ∀ (i : Fin μ.r) (mi : ℕ) (v : Fin mi → Fin m → ℝ), IsRankOneDecomp (μ.W i) v →
          ∀ l, evalP P (sE sv) (μ.pts i) *ᵥ v l = 0) := by sorry

end RobustPMI.Hierarchy.Supplement
