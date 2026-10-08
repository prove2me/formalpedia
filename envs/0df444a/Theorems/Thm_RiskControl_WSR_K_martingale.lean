-- Prove2me | Theorems.Thm_RiskControl_WSR_K_martingale
-- name    : RiskControl.WSR.K_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:52.634747+00:00
-- url     : https://prove2.me/theorems/e757d735-3abe-45e6-b88b-72a961c0c3ef
-- title:
--   Proof of Proposition 5, p. 26 — at the true mean R, the capital process 𝒦ᵢ(R) is a martingale for σ(L₁, …, Lᵢ)
-- statement:
--   Let $Q$ be a probability measure on $\mathbb R$ concentrated on $[0,1]$, let $R = \int x\, dQ(x)$ be its mean, let $n \in \mathbb N$ and $\delta \in \mathbb R$, and let the sample $\omega = (L_1, \dots, L_n)$ have the product law $Q^{\otimes n}$, so that $L_1, \dots, L_n$ are i.i.d. with law $Q$. Let $\mathcal K_i(R)$ be the capital process of Proposition 5 and $\mathcal F_i = \sigma(L_1, \dots, L_i)$ (see the definition `RiskControl.WSR.Process`). Then the process
--   $$i \mapsto \mathcal K_{\min(i,n)}(R), \qquad i = 0, 1, 2, \dots$$
--   is a martingale with respect to $(\mathcal F_i)_{i \ge 0}$ under $Q^{\otimes n}$; in particular, for $1 \le i \le n$,
--   $$\mathbb E\bigl[\mathcal K_i(R) \mid \mathcal F_{i-1}\bigr] = \mathcal K_{i-1}(R).$$
--
--   This is the martingale property at the heart of the proof of Proposition 5: since $\nu_i$ is $\mathcal F_{i-1}$-measurable and $\mathbb E[L_i] = R$, betting against the true mean does not change the expected capital.
--
--   **Formalization Note** $Q$ is the law of the loss $L(Y, \mathcal T_\lambda(X))$ for the fixed $\lambda$, which lies in $[0,1]$ by the standing assumption of §3.1; the losses of the $n$ i.i.d. calibration points are then i.i.d. with law $Q$. The paper's martingale is indexed by $i = 0, \dots, n$ with $\mathcal F_0$ trivial and $\mathcal K_0 = 1$; it is extended constantly past $n$ (index $\min(i,n)$, with $\mathcal F_i = \mathcal F_n$ for $i \ge n$), so that it is a process indexed by $\mathbb N$, as Mathlib's `Martingale` requires. The nonnegativity half of the paper's sentence ("non-negative martingale") is the separate item `RiskControl.WSR.factor_nonneg`. No condition on $\delta$ is needed: $\nu_i \in [0,1]$ is predictable for every real $\delta$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Proposition 5, p. 26, first display and the sentences around it

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

open MeasureTheory

namespace RiskControl.WSR

/-- Proof of Proposition 5, p. 26 (arXiv:2101.02703v3): at the true mean `R = ∫ x dQ` of the
`[0, 1]`-valued losses, the capital process `𝒦_i = 𝒦_i(R; λ)`, `i = 0, …, n`, is a martingale
for the natural filtration `ℱ_i = σ(L_1, …, L_i)` under the i.i.d. law `Qⁿ`; it is extended
constantly past `n` (index `min i n`) to a process indexed by `ℕ`. -/
theorem K_martingale (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (δ : ℝ) :
    Martingale (fun i (ω : Fin n → ℝ) => K n δ ω (min i n) (∫ x, x ∂Q)) (filt n)
      (Measure.pi fun _ : Fin n => Q) := by sorry

end RiskControl.WSR
