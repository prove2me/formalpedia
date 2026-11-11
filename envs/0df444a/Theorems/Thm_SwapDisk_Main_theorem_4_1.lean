-- Prove2me | Theorems.Thm_SwapDisk_Main_theorem_4_1
-- name    : SwapDisk.Main.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:19:28.135306+00:00
-- url     : https://prove2.me/theorems/73cae539-d055-4ae3-8642-c71f32cd8a06
-- title:
--   Theorem 4.1 — SHARP master bound: $\le1+C_{\mathrm{cov}}\gamma^{-1/2}$ points, $R_T\le R^{\mathrm{tag}}_T\le C_{\mathrm{par}}(\gamma T+(1+U)/\gamma)$, $\mathbb EU<1$
-- statement:
--   Let $C_{\mathrm{par}}=2^{24}$. For every integer $T\ge2$ and $\gamma\in\Gamma_T$, SHARP (any nets satisfying (B.3), any fixed Borel response selector with error $1/T$) uses at most $1+C_{\mathrm{cov}}\gamma^{-1/2}$ predetermined physical points, $C_{\mathrm{cov}}=256/(1-2^{-1/2})$. Uniformly over admissible adversaries, with $U=\log(1+\Psi_T)$,
--   $$R_T\le R^{\mathrm{tag}}_T\le C_{\mathrm{par}}\Big(\gamma T+\frac{1+U}\gamma\Big),\qquad\mathbb EU<1 ,$$
--   and moreover $\mathbb E\Psi_T\le e^{1/16}$ and $\mathbb ER_T\le C_{\mathrm{par}}(\gamma T+2/\gamma)$.
--
--   This single master bound, uniform in the resolution, gives every upper bound of the paper.
--
--   Differences from the source:
--   - encoding: SHARP (Algorithm 4.1, Eqs. (B.18)–(B.24)) in the canonical tagged experiment of §A.3 → `sharpLaw sel D T`: the tagged law of the Sharp/TagExperiment definitions; weights as closed-form products; tag draw `∑_j q_t(j) δ_j`; reason: the product form equals the recursion (B.21); the law is the ordered-kernel law of §A.3
--   - encoding: γ ∈ Γ_T = {2^{−k} : 0 ≤ k ≤ ⌊log₂ T⌋} → γ = `gam ell` = 2^{−ℓ} with `ell ≤ Nat.log 2 T`; reason: the same set of resolutions, indexed by ℓ_γ = log₂(1/γ)
--   - encoding: angular r_s-nets X_s ⊆ S¹ with |X_s| ≤ 16/r_s (Eq. (B.3)), angular distance = shorter arc → `NetsOK ell X`: `X k` a `Finset` of unit vectors, every unit `u` within `arccos ⟨u, x⟩ ≤ r_k` of some `x ∈ X k`, and `card (X k) ≤ 16 / r_k`; reason: arccos⟨u, x⟩ is the length of the shorter arc between unit vectors; same nets
--   - generalization: any fixed Borel response selector satisfying Proposition B.3 with error at most 1/T → any `sel` with `IsResponseSelector (1/T) sel`: Borel, Δ(J)-valued on Δ(C), with L_κ(sel κ, g) ≤ 1/T (Eq. (B.12)); dyadic coordinates not required; reason: only (B.12) is used by SHARP's analysis; a selector with dyadic coordinates (the B.3 selector) is a special case
--   - generalization: uniformly over admissible adversaries → every `TagAdversary`: kernels on the tag–loss history (past tags, losses, hence every past announcement, past point and the current tag law q_t); reason: this is the stronger adversary the upper-bound analysis permits (p. 14, §A.3); every adversary of the public protocol is one, by composing its kernels with the map from tag–loss histories to public histories
--   - encoding: E[·] and P{·} under the canonical law → Bochner integrals and measures of events under `law`/`sharpLaw` (`ENNReal.ofReal p ≤ μ {…}` for P{…} ≥ p); reason: the integrands are bounded Borel functions (Proposition A.1); same values
--   - encoding: pathwise R_T ≤ R^tag_T ≤ C_par(γT + (1 + U)/γ) → for every tag–loss history h ∈ (J × B²₂)^T; reason: the inequality is deterministic in the realized transcript
--   - encoding: number of predetermined physical points → card of the image of `tagPt` over all tags; reason: distinct physical points of the dictionary
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 10, Theorem 4.1

import Mathlib
import Definitions.Def_SwapDisk_Main_TagExperiment

open MeasureTheory

namespace SwapDisk.Main

/-- Theorem 4.1 (Uniform-resolution disk bound), p. 10: with `C_par = 2^24`, for every integer
`T ≥ 2` and `γ = 2^{−ℓ} ∈ Γ_T`, SHARP (any nets satisfying (B.3), any Borel response selector with
error `1/T`) uses at most `1 + C_cov γ^{−1/2}` predetermined physical points; pathwise
`R_T ≤ R^tag_T ≤ C_par(γT + (1 + U)/γ)` with `U = log(1 + Ψ_T)`; and uniformly over admissible
adversaries `EU < 1`, `EΨ_T ≤ e^{1/16}`, `ER_T ≤ C_par(γT + 2/γ)`. -/
theorem theorem_4_1 (T ell : ℕ) (hT : 2 ≤ T) (hell : ell ≤ Nat.log 2 T)
    (X : Fin (ell + 1) → Finset E2) (hX : NetsOK ell X)
    (sel : (Con ell X → ℝ) → (Tag ell X → ℝ)) (hsel : IsResponseSelector (1 / (T : ℝ)) sel) :
    ((Finset.univ.image (tagPt (ell := ell) (X := X))).card : ℝ) ≤
        1 + 256 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) * gam ell ^ (-(1 / 2 : ℝ)) ∧
    (∀ h : Fin T → Tag ell X × Disk,
      physRegret h ≤ tagRegret h ∧
      tagRegret h ≤ (2 : ℝ) ^ 24 * (gam ell * T + (1 + Ubudget h) / gam ell)) ∧
    ∀ D : TagAdversary (Tag ell X),
      ∫ z, Ubudget (TagTraj.hist z) ∂(sharpLaw sel D T) < 1 ∧
      ∫ z, Psi (TagTraj.hist z) ∂(sharpLaw sel D T) ≤ Real.exp (1 / 16) ∧
      ∫ z, physRegret (TagTraj.hist z) ∂(sharpLaw sel D T) ≤
        (2 : ℝ) ^ 24 * (gam ell * T + 2 / gam ell) := by sorry

end SwapDisk.Main
