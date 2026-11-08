-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_15
-- name    : SpencerEight.lemma_8_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:03.899365+00:00
-- url     : https://prove2.me/theorems/b5513c81-edfa-41f1-9566-efe3b57eaa25
-- title:
--   Lemma 8.15 — Gaussian transfer with a scalar cap
-- statement:
--   Let $\kappa,\eta>0$, let $\Gamma\succeq0$ be an $m\times m$ matrix with $\operatorname{tr}\Gamma\le N\eta$ and $\operatorname{rank}\Gamma\le wN$, let $\nu$ be the probability measure proportional to $e^{-\kappa\xi^\top\Gamma\xi}d\gamma_m(\xi)$, and put $\omega_j:=\operatorname{tr}[\Gamma(I+2\kappa\Gamma)^{-j}]/(N\eta)$. Suppose a Borel set $\mathcal K$ satisfies $-N^{-1}\log\nu(\mathcal K)\le C+\sum_jQ_j\omega_j$, with $C,Q_j\ge0$ and finitely many coefficients. For $H>1$, $b\ge0$, $B_{\mathrm{cap}}>0$, if
--   $$L_H(x)+\frac{H}{(H-1)\kappa\eta}\sum_j\frac{Q_j}{(1+x)^j}-\frac bx\le B_{\mathrm{cap}}\qquad(x>0),$$
--   then
--   $$\gamma_m(\mathcal K)\ge e^{-Ne},\qquad e:=\kappa\eta B_{\mathrm{cap}}+bw/2+\frac{HC}{H-1}.\tag{74}$$
--   For $b=0$ include the continuous value at zero, and no rank condition is needed. The same cap gives exponent at most $\alpha e$ after replacing $\eta,w,C,Q_j$ by $\alpha\eta,\alpha w,C_\alpha,Q_{j,\alpha}$, provided $0<\alpha\le1$, $C_\alpha\le\alpha C$ and $Q_{j,\alpha}\le\alpha Q_j$.
--
--   The lemma returns a bound under the tilted measure to the standard Gaussian, and the scaling clause makes the bound hereditary.
--
--   Differences from the source:
--   - encoding: −N⁻¹ log ν(K) ≤ C + Σ Q_j ω_j → exp(−N(C + Σ Q_j ω_j)) ≤ ν(K), with 0 < N; reason: the same inequality for N > 0, and it excludes ν(K) = 0, which Real.log 0 = 0 would admit
--   - reading: For b = 0 include the continuous value at zero → the hypothesis, under b = 0, that the cap also holds at x = 0; reason: it is the only reading as a condition; it follows from the cap on x > 0 by continuity, so it removes no instance
--   - reading: The same cap gives exponent at most αe after replacing η, w, C, Q_j → for (Γ, K) satisfying the hypotheses at (αη, αw, C_α, Q_{j,α}), with 0 ≤ C_α and 0 ≤ Q_{j,α} and with the cap taken at the original (η, Q_j), one has exp(−Nαe) ≤ γ_m(K), e the original exponent; reason: "the same cap" is the cap at the original parameters, as in the page's proof
--   - encoding: rank Γ ≤ wN as a hypothesis, and "When b = 0 no rank condition is needed" → rank Γ ≤ wN assumed only under b ≠ 0; reason: the conjunction of the two sentences; at b ≠ 0 the hypothesis is the printed one, at b = 0 it is dropped as the page says
--   - encoding: Σ_j over finitely many coefficients → a sum over a Finset J of exponents; reason: "with finitely many coefficients"
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.15, pp.78–79 (PDF pp.78–79)

import Mathlib
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_LH
import Definitions.Def_SpencerEight_TransferData

namespace SpencerEight

/-- Lemma 8.15 (Gaussian transfer with a scalar cap), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), pp.78–79 (PDF pp.78–79). Eq. (74) and the scaling clause.

**Formalization Note** The scalar cap is fixed first, then `(Γ, K)` range over `TransferData`. The rank condition sits inside `TransferData`, under `b ≠ 0`. "For `b = 0` include the continuous value at zero" is the hypothesis `hzero`; it follows from the cap on `x > 0` by continuity. `N > 0` because the page divides by `N`. -/
theorem lemma_8_15 {m N : ℕ} (hN : 0 < N) {κ η H b Bcap C w : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    (hH : 1 < H) (hb : 0 ≤ b) (hBcap : 0 < Bcap) (J : Finset ℕ) (Q : ℕ → ℝ)
    (hcap : ∀ x : ℝ, 0 < x →
      LH H x + H / ((H - 1) * κ * η) * ∑ j ∈ J, Q j / (1 + x) ^ j - b / x ≤ Bcap)
    (hzero : b = 0 → LH H 0 + H / ((H - 1) * κ * η) * ∑ j ∈ J, Q j ≤ Bcap) :
    (∀ (Γ : Matrix (Fin m) (Fin m) ℝ) (K : Set (Fin m → ℝ)), TransferData N κ η w b C J Q Γ K →
      ENNReal.ofReal (Real.exp (-(N * (κ * η * Bcap + b * w / 2 + H * C / (H - 1))))) ≤
        gammaM (Fin m) K) ∧
    (∀ (α Cα : ℝ) (Qα : ℕ → ℝ), 0 < α → α ≤ 1 → Cα ≤ α * C → (∀ j ∈ J, Qα j ≤ α * Q j) →
      ∀ (Γ : Matrix (Fin m) (Fin m) ℝ) (K : Set (Fin m → ℝ)),
        TransferData N κ (α * η) (α * w) b Cα J Qα Γ K →
        ENNReal.ofReal (Real.exp (-(N * (α * (κ * η * Bcap + b * w / 2 + H * C / (H - 1)))))) ≤
          gammaM (Fin m) K) := by sorry

end SpencerEight
