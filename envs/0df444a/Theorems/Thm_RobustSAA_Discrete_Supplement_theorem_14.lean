-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_14
-- name    : RobustSAA.Discrete.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:46:39.474973+00:00
-- url     : https://prove2.me/theorems/6c3767e3-3405-4b7d-a738-682927d61cec
-- title:
--   Theorem 14 (corrected: signed w, w′; lower bound uses the region's moment bound and +L·c(x;ξ′)/‖ξ′‖²) — LCX worst case bracketed by the LP C′
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed, $K\ge1$, and $c(x;\xi)=\max_kc_k(x;\xi)$ on $\Xi$ as in (37), each $c_k(x;\cdot)$ concave and upper semicontinuous on $\Xi$. Let $c_{k*}$ be the concave conjugates, $\mathcal G=\{0,1\}^K\setminus\{0\}$, $C'(x;\nu,\eta)$ the optimal value of (38)–(39), data $\xi^1,\dots,\xi^N\in\Xi$ ($N\ge1$) and $\mathcal F=\mathcal F^{\alpha_1,\alpha_2}_{C_N,R_N}$ the region (17) with thresholds $Q_C,Q_R$. Write $L=\max\{\frac1N\sum_i\|\xi^i\|_2^2-Q_R,\,0\}$ for the lower bound on $\mathbb E_{F_0}[\|\xi\|_2^2]$ in (17). Assume the hypotheses of Theorem 1 for $\mathcal F$ and $c(x;\cdot)$ measurable. Then for every $x\in X$:
--
--   1. $C(x;\mathcal F)\le C'(x;Q_C,1)$.
--   2. If $Q_C>0$ and $Q_R>0$, then for every $\xi'_0\in\Xi$ with $\xi'_0\ne0$,
--   $$C(x;\mathcal F)\ge C'\Big(x;\,Q_C-\frac{\|\xi'_0\|_2+1}{\|\xi'_0\|_2^2}L,\ 1-\frac L{\|\xi'_0\|_2^2}\Big)+\frac{L\,c(x;\xi'_0)}{\|\xi'_0\|_2^2}.$$
--   3. If $Q_C>0$, $Q_R>0$ and there are $\xi'_i\in\Xi$ with $\|\xi'_i\|\to\infty$ and $\limsup_i c(x;\xi'_i)/\|\xi'_i\|_2^2\ge0$ (condition (40)), then $C(x;\mathcal F)=C'(x;Q_C,1)$.
--
--   The program $C'$ is a finite linear program (given conjugate oracles), so the theorem brackets, and under (40) computes, the LCX worst case.
--
--   Differences from the source:
--   - reading: c(x;ξ) as in (37) with each c_k closed concave in ξ → c = max_k c_k on Ξ, K ≥ 1, each c_k(x;·) real-valued, concave and upper semicontinuous on Ξ (so Ξ is convex); reason: closed concave = concave and upper semicontinuous; concavity on Ξ needs a convex domain; the pieces of a real cost are taken real-valued (a piece equal to −∞ somewhere is not represented)
--   - correction: w ∈ ℝ₊^{|𝒢|×d}, w′ ∈ ℝ₊^{|𝒢|} in (38) → w, w′ sign-free; reason: §10.17 introduces them as multipliers of the equality constraints Σγ_k q_k − (1/N)Σμ_{γ,i}ξⁱ = u_γ − v_γ and −Σγ_k p_k + (1/N)Σμ_{γ,i} = u′_γ − v′_γ; h_k = Σγ_k w_γ must range over ℝ^d; the constraints ±w ≤ y linearize |w|
--   - correction: lower bound with Q_{R_N}(α₂) in C′ and −c(x;ξ′₀)/‖ξ′₀‖² → lower bound with L = max{(1/N)Σ‖ξⁱ‖² − Q_R, 0} in C′ and + L·c(x;ξ′₀)/‖ξ′₀‖²; reason: §10.17 treats Q_R as the absolute lower bound ⟨F,‖ξ‖²⟩ ≥ Q_R, whereas (17) bounds E_{F₀}‖ξ‖² below by the empirical mean minus Q_R (a negative bound can be replaced by 0); substituting τ ≤ (θ + (R+1)G(S) − c(x;ξ′₀))/R² into −Lτ gives +L·c(x;ξ′₀)/R²; with c(x;ξ′₀) < 0 and a small moment bound the printed form contradicts part 1
--   - correction: the lower bound and the equality for all thresholds → assume Q_C > 0 and Q_R > 0; reason: §10.17 uses the empirical distribution as generalized Slater point (Proposition 2.8 of [45]), strictly feasible exactly when both thresholds are positive; part 1 keeps all thresholds; excluded: Q_C ≤ 0 or Q_R ≤ 0 in parts 2–3
--   - encoding: for any ξ′₀ ∈ Ξ → for any ξ′₀ ∈ Ξ with ξ′₀ ≠ 0; reason: the bound divides by ‖ξ′₀‖₂², undefined at ξ′₀ = 0
--   - encoding: limsup_i c(x;ξ′ᵢ)/‖ξ′ᵢ‖₂² ≥ 0 → for every ε > 0, frequently c(x;ξ′ᵢ)/‖ξ′ᵢ‖₂² ≥ −ε; reason: extended-real limsup, avoiding the real limsup default
--   - encoding: C′ defined by min → C′ is the extended-real infimum of (38)–(39); reason: the theorem compares values; attainment is not part of its conclusion
--   - reading: a cost whose expectations E_{F₀}[c(x;ξ)] are taken → c(x;·) is measurable for every x; reason: expectations of c(x;·) presuppose measurability; standing convention of the field
--   - encoding: E_{F₀}[c(x;ξ)] for any law → the integral when c(x;·) is F₀-integrable and +∞ otherwise (the published RobustSAA.Convergence.expect convention); reason: series convention; a member under which the cost is not integrable never lowers a worst case
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 14, p. 21 (proof §10.17, pp. 43–45)

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX
import Definitions.Def_RobustSAA_Discrete_Supplement_LCXDual

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence

theorem theorem_14 {d dx K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set (Pt d))
    (hΞ : IsClosed Ξ) (X : Set (Pt dx)) (hX : IsClosed X) (c : Pt dx → Pt d → ℝ)
    (ck : Fin K → Pt dx → Pt d → ℝ)
    (hmax : ∀ x, ∀ ξ ∈ Ξ, (∀ k, ck k x ξ ≤ c x ξ) ∧ ∃ k, c x ξ = ck k x ξ)
    (hconc : ∀ k x, ConcaveOn ℝ Ξ (ck k x)) (husc : ∀ k x, UpperSemicontinuousOn (ck k x) Ξ)
    (hmeas : ∀ x, Measurable (fun ξ : ↥Ξ => c x (ξ : Pt d)))
    (hequi : Assumption1 X (fun x (ξ : ↥Ξ) => c x (ξ : Pt d)))
    (hcomp : IsCompact X ∨ ∀ ξ ∈ Ξ, Tendsto (fun x => c x ξ) (Bornology.cobounded (Pt dx)) atTop)
    (s : Fin N → ↥Ξ) (QC QR : ℝ)
    (hx₀ : ∃ x₀ ∈ X, worstCase (lcxRegion QC QR s) (fun ξ : ↥Ξ => c x₀ (ξ : Pt d)) < ⊤)
    (x : Pt dx) (hx : x ∈ X) :
    worstCase (lcxRegion QC QR s) (fun ξ : ↥Ξ => c x (ξ : Pt d)) ≤ lcxCprime Ξ ck x s QC 1 ∧
    (0 < QC → 0 < QR → ∀ ξ₀ ∈ Ξ, ξ₀ ≠ 0 →
      lcxCprime Ξ ck x s
          (QC - (‖ξ₀‖ + 1) / ‖ξ₀‖ ^ 2 * max (empSecondMoment s - QR) 0)
          (1 - max (empSecondMoment s - QR) 0 / ‖ξ₀‖ ^ 2) +
        ((max (empSecondMoment s - QR) 0 * c x ξ₀ / ‖ξ₀‖ ^ 2 : ℝ) : EReal) ≤
      worstCase (lcxRegion QC QR s) (fun ξ : ↥Ξ => c x (ξ : Pt d))) ∧
    (0 < QC → 0 < QR → (∃ ξs : ℕ → Pt d, (∀ i, ξs i ∈ Ξ) ∧ Tendsto (fun i => ‖ξs i‖) atTop atTop ∧
        ∀ ε : ℝ, 0 < ε → ∃ᶠ i in atTop, -ε ≤ c x (ξs i) / ‖ξs i‖ ^ 2) →
      worstCase (lcxRegion QC QR s) (fun ξ : ↥Ξ => c x (ξ : Pt d)) =
        lcxCprime Ξ ck x s QC 1) := by sorry

end RobustSAA.Discrete.Supplement
