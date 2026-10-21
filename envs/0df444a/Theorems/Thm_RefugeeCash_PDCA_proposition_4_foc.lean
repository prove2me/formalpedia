-- Prove2me | Theorems.Thm_RefugeeCash_PDCA_proposition_4_foc
-- name    : RefugeeCash.PDCA.proposition_4_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:16.382988+00:00
-- url     : https://prove2.me/theorems/0e74a545-e50d-4487-925e-6b31e733aa5a
-- title:
--   Proof of Proposition 4, Online Appendix p. 5 (PDF 37) — the PDCA policy (22)–(24) pays (k⊙, g⊙) at p⊙, and p = p⊙ satisfies the first-order condition (A.13)
-- statement:
--   Consider the $n$-good model with target prices $\mathbf p^\odot \in \mathbb R^n$, target cash fraction $k^\odot$ and target in-kind assistance $\mathbf g^\odot$. Let $\tilde\pi_r(\mathbf p,k) = \pi_r(\mathbf p,k,\mathbf g^\odot(1-k)/(1-k^\odot))$ as in (15), and let the PDCA policy be given by the weights $v_i = \partial\Pi(\mathbf p^\odot,k^\odot,\mathbf g^\odot)/\partial p_i$ of (22), the cash fraction $k(p_{\mathbf v}) = \min\{(a+s\,p_{\mathbf v})^+,1\}$ with $s = -(\partial\tilde\pi_r(\mathbf p^\odot,k^\odot)/\partial k)^{-1}$ and $a = k^\odot - s\,\mathbf p^{\odot\top}\mathbf v$ of (23), and the in-kind assistance $\mathbf g(p_{\mathbf v}) = \mathbf g^\odot(1-k(p_{\mathbf v}))/(1-k^\odot)$ of (24).
--
--   Assume
--   1. $0 < k^\odot < 1$;
--   2. $(\mathbf p,k) \mapsto \tilde\pi_r(\mathbf p,k)$ is differentiable at $(\mathbf p^\odot,k^\odot)$ and $\pi_0$ is differentiable at $\mathbf p^\odot$;
--   3. $\partial\tilde\pi_r(\mathbf p^\odot,k^\odot)/\partial k \neq 0$.
--
--   Then pricing at $\mathbf p^\odot$ yields the target assistance, $k(\mathbf p^{\odot\top}\mathbf v) = k^\odot$ and $\mathbf g(\mathbf p^{\odot\top}\mathbf v) = \mathbf g^\odot$, and the retailer's PDCA objective satisfies the first-order condition at the target prices:
--   $$\nabla_{\mathbf p}\Big[\tilde\pi_r\big(\mathbf p, k(\mathbf p^\top\mathbf v)\big) + \pi_0(\mathbf p)\Big]\Big|_{\mathbf p = \mathbf p^\odot} = \mathbf 0 .$$
--
--   This is the paper's general incentive design: the weights of the price index are the retailer's marginal profits at the target, and the sensitivity $s$ of the cash fraction exactly offsets the marginal gain from raising any price.
--
--   **Formalization Note** This is the claim verified in the proof of Proposition 4 (Online Appendix p. 5): the assistance at $\mathbf p^\odot$ is $(k^\odot,\mathbf g^\odot)$, and "$\mathbf p = \mathbf p^\odot$ satisfies (A.13)". It is **not** Proposition 4's conclusion that $\mathbf p^\odot$ maximizes the retailer's profit, i.e. (16): the proof passes from (A.13) to (16) only "under most common demand functions", a condition the paper never states, and without such a condition (16) can fail while (A.13) holds. The Lean states the first-order condition as a zero Fréchet derivative of the objective at $\mathbf p^\odot$. Three hypotheses are added: $0 < k^\odot < 1$ (equation (24) divides by $1-k^\odot$, and the clip in (23) must be inactive near $\mathbf p^\odot$), $\partial\tilde\pi_r/\partial k \ne 0$ (since $s$ is its inverse), and the differentiability the page takes for granted.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), proof of Proposition 4, Online Appendix p. 5 (PDF 37), eq. (A.13); policy (22)–(24) of Proposition 4, pp. 19–20 (PDF 20–21)

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

namespace RefugeeCash.PDCA

open GenParams

/-- Proof of Proposition 4, Online Appendix p. 5 (PDF 37): with the weights `v` of (22), the cash
fraction `k(·)` of (23) and the in-kind assistance `g(·)` of (24), pricing at `p⊙` yields the
assistance `(k⊙, g⊙)`, and `p = p⊙` satisfies the retailer's first-order condition (A.13): the
PDCA objective `π̃r(p, k(pᵀv)) + π0(p)` has zero derivative at `p⊙`. This is the claim the proof
verifies; it is not Proposition 4's global optimality (16), which the proof derives from (A.13)
only "under most common demand functions". -/
theorem proposition_4_foc {n : ℕ} (M : GenParams n) (pT gT : Fin n → ℝ) (kT : ℝ)
    (hk : 0 < kT ∧ kT < 1)
    (hR : DifferentiableAt ℝ (fun x : (Fin n → ℝ) × ℝ => M.piRtilde kT gT x.1 x.2) (pT, kT))
    (h0 : DifferentiableAt ℝ M.pi0 pT)
    (hs : deriv (fun k => M.piRtilde kT gT pT k) kT ≠ 0) :
    M.kOf pT kT gT (pT ⬝ᵥ M.vPDCA pT kT gT) = kT ∧
      M.gOf pT kT gT (pT ⬝ᵥ M.vPDCA pT kT gT) = gT ∧
      HasFDerivAt (M.pdcaProfitGen pT kT gT) (0 : (Fin n → ℝ) →L[ℝ] ℝ) pT := by sorry

end RefugeeCash.PDCA
