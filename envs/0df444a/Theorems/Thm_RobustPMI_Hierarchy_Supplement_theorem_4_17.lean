-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_4_17
-- name    : RobustPMI.Hierarchy.Supplement.theorem_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:45:00.58393+00:00
-- url     : https://prove2.me/theorems/32f1eab4-dbdb-4a30-8e17-27953fa78847
-- title:
--   Theorem 4.17, p. 26 — robust polynomial SDP: τ_k^primal ↘ τ⋆ and τ_k^dual ↘ τ⋆
-- statement:
--   Consider the robust polynomial semidefinite program
--   $$\tau^\star=\inf_{y\in\mathbb R^\ell}c^\top y\quad\text{s.t.}\quad\sum_{i=1}^\ell P_i(x)y_i-P_0(x)\succeq0\ \ \forall x\in\mathcal X,\tag{RPSDP}$$
--   with $c\in\mathbb R^\ell$, $P_0,\dots,P_\ell\in\mathbb S[x]^m$, and its relaxations (4.14) $\tau_k^{\mathrm{primal}}=\sup\{\mathscr L_S(P_0):S\in\mathcal M^m_k(G),\ \mathscr L_S(P_i)=c_i\}$ and (4.15) $\tau_k^{\mathrm{dual}}=\inf\{c^\top y:\sum_iP_iy_i-P_0\in\mathcal Q^m_k(G)\}$. Let Assumption 2 (Archimedean condition) and Assumption 3 (a Slater point $\bar y$ with $\sum_iP_i(x)\bar y_i-P_0(x)\succ0$ on $\mathcal X$) hold, and assume (RPSDP) has an optimal solution. Then
--
--   1. $\tau_k^{\mathrm{primal}}\searrow\tau^\star$ and $\tau_k^{\mathrm{dual}}\searrow\tau^\star$ as $k\to\infty$ (non-increasing for $k\ge\lceil k_x/2\rceil$);
--   2. if $y^{(k,\star)}$ is an optimal solution of (4.15) for every sufficiently large $k$, the limit of any convergent subsequence $(y^{(k_i,\star)})_i$ is an optimal solution of (RPSDP).
--
--   **Formalization Note** $k_x=\max(\deg P_0,\dots,\deg P_\ell,\deg G)$.
--
--   Differences from the source:
--   - reading: the theorem's own hypotheses ((RPSDP) is a special case of (RPMIO), whose optimal set is assumed nonempty on p. 2) → hypothesis ∃ y, IsOptSDP c P0 Pv G y; reason: the p. 2 standing assumption governs every statement about τ⋆; without it the real infimum τ⋆ is a junk value
--   - reading: y^{(k,⋆)} optimal for (4.15) for each k → y^{(k,⋆)} optimal for all sufficiently large k (∀ᶠ k in atTop); reason: the minimizers need only exist from some order on, as the paper presupposes; same reading as the published Theorem 4.9
--   - encoding: '↘' and the values in ℝ ∪ {±∞} → AntitoneOn on k ≥ ⌈k_x/2⌉ and Tendsto in EReal; reason: Lean convention, as in the published Theorem 4.9
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 26, Theorem 4.17

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 4.17 (p. 26): for (RPSDP) under Assumptions 2–3 (and the standing assumption that
(RPSDP) has an optimal solution),
(i) `τ_k^primal ↘ τ⋆` and `τ_k^dual ↘ τ⋆` as `k → ∞`;
(ii) if `y^{(k,⋆)}` is an optimal solution of (4.15) for all large `k`, the limit of every
convergent subsequence `(y^{(k_i,⋆)})_i` is an optimal solution of (RPSDP). -/
theorem theorem_4_17 {ℓ n m q : ℕ} (c : Fin ℓ → ℝ)
    (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP0 : P0.IsSymm) (hPv : ∀ i, (Pv i).IsSymm) (hG : G.IsSymm)
    (h2 : Assumption2 G) (h3 : Assumption3SDP P0 Pv G)
    (hmin : ∃ y, IsOptSDP c P0 Pv G y) :
    (AntitoneOn (tauprimal c P0 Pv G) (Set.Ici ((kxSDP P0 Pv G + 1) / 2)) ∧
      AntitoneOn (taudual c P0 Pv G) (Set.Ici ((kxSDP P0 Pv G + 1) / 2)) ∧
      Tendsto (tauprimal c P0 Pv G) atTop (𝓝 (taustar c P0 Pv G : EReal)) ∧
      Tendsto (taudual c P0 Pv G) atTop (𝓝 (taustar c P0 Pv G : EReal))) ∧
    (∀ yq : ℕ → Fin ℓ → ℝ, (∀ᶠ k in atTop, IsTauDualOpt c P0 Pv G k (yq k)) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ystar : Fin ℓ → ℝ,
        Tendsto (fun i => yq (φ i)) atTop (𝓝 ystar) → IsOptSDP c P0 Pv G ystar) := by sorry

end RobustPMI.Hierarchy.Supplement
