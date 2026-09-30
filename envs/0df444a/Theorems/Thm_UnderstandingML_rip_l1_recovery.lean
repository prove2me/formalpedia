-- Prove2me | Theorems.Thm_UnderstandingML_rip_l1_recovery
-- name    : UnderstandingML.rip_l1_recovery
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:25:22.360592+00:00
-- url     : https://prove2.me/theorems/5f139244-e820-4030-baf5-ff5cbe52b3af
-- title:
--   Theorem 23.8 (Candès): for ε < 1/(1+√2) and W (ε,2s)-RIP, the ℓ₁-minimizer x⋆ with Wx⋆ = Wx has ‖x⋆ − x‖₂ ≤ 2(1+ρ)/(1−ρ) s^{−1/2}‖x − x_s‖₁, ρ = √2ε/(1−ε)
-- statement:
--   **Theorem 23.8.** Let $\epsilon < \frac1{1+\sqrt2}$ and let $W$ be an $(\epsilon, 2s)$-RIP matrix. Let $x$ be an arbitrary vector and denote $x_s \in \operatorname{argmin}_{v : \|v\|_0 \le s}\|x - v\|_1$, the vector which equals $x$ on the $s$ largest elements of $x$ and equals $0$ elsewhere. Let $y = Wx$ be the compression of $x$ and let $x^\star \in \operatorname{argmin}_{v : Wv = y}\|v\|_1$ be the reconstructed vector. Then
--   $$\|x^\star - x\|_2 \le 2\frac{1+\rho}{1-\rho}\, s^{-1/2}\|x - x_s\|_1, \qquad \rho = \sqrt2\epsilon/(1-\epsilon).$$
--
--   Formally: $s \ge 1$, $0 \le \epsilon$, $x_s$ any minimizer of $\|x - v\|_1$ over $\|v\|_0 \le s$, $x^\star$ any $\ell_1$-minimizer subject to $Wv = Wx$; the proof's simplifying assumption that $d/s$ is an integer is not needed.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.3 p. 332, Theorem 23.8, proved in §23.3.1 pp. 333-335 (Candès 2008)

import Definitions.Def_UnderstandingML_DimReduction

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

/-- **Theorem 23.8 (Candès 2008)** (p. 332). Let `ε < 1/(1 + √2)` and let `W` be an
`(ε, 2s)`-RIP matrix. Let `x` be an arbitrary vector and denote `x_s ∈ argmin_{v : ‖v‖₀ ≤ s} ‖x − v‖₁`
(the vector which equals `x` on the `s` largest elements of `x` and `0` elsewhere). Let `y = Wx`
and let `x⋆ ∈ argmin_{v : Wv = y} ‖v‖₁` be the reconstructed vector. Then
`‖x⋆ − x‖₂ ≤ 2 (1 + ρ)/(1 − ρ) s^{−1/2} ‖x − x_s‖₁`, where `ρ = √2 ε/(1 − ε)`. `s ≥ 1`. -/
theorem rip_l1_recovery {n d s : ℕ} (hs : 0 < s) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (1 + Real.sqrt 2)) (W : Matrix (Fin n) (Fin d) ℝ) (hW : IsRIP ε (2 * s) W)
    (x xs xstar : Fin d → ℝ) (hxs : l0Norm xs ≤ s)
    (hxs_min : ∀ v, l0Norm v ≤ s → l1Norm (x - xs) ≤ l1Norm (x - v))
    (hy : W.mulVec xstar = W.mulVec x)
    (hmin : ∀ v, W.mulVec v = W.mulVec x → l1Norm xstar ≤ l1Norm v) :
    Real.sqrt (sqNorm (xstar - x)) ≤
      2 * (1 + Real.sqrt 2 * ε / (1 - ε)) / (1 - Real.sqrt 2 * ε / (1 - ε)) *
        (s : ℝ) ^ (-(1 : ℝ) / 2) * l1Norm (x - xs) := by sorry

end UnderstandingML
